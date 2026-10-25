//! Combined-file assembly and the explicit InputMapping-to-generic-export adapter.
use crate::{
    ast::Program,
    lowering::{self, FilePlacement, LoweredProgram, LoweringOutcome},
    syntax::{self, ParseOutcome},
};
use denotate_editor::Document;
use denotate_ir::*;
use denotate_ir_text::*;
use std::collections::{BTreeMap, BTreeSet};

pub struct Assembled {
    pub sources: Sources,
    pub program: LoweredProgram,
}
/// Sort canonical identities, parse each file separately, then validate/lower once.
pub fn assemble(documents: &[SourceFile]) -> std::result::Result<Assembled, Vec<Diagnostic>> {
    let mut sources = Sources::new();
    let mut ast = Program::default();
    let mut seen = BTreeSet::new();
    let mut documents = documents.iter().collect::<Vec<_>>();
    documents.sort_by(|a, b| a.uri.cmp(&b.uri));
    let fail = |uri: &str, message: String| {
        vec![Diagnostic {
            uri: uri.into(),
            range: 0..0,
            message,
        }]
    };
    for source in documents {
        if !seen.insert(&source.uri) {
            return Err(fail(&source.uri, "Repeated canonical input file".into()));
        }
        let snapshot = sources
            .add(
                &source.uri,
                source.revision,
                "test-dsl",
                source.text.clone(),
            )
            .map_err(|e| fail(&source.uri, e.to_string()))?;
        let doc = Document::new(
            &mut syntax::parser().map_err(|e| fail(&source.uri, e.to_string()))?,
            source.text.to_string(),
            1,
            false,
        );
        match syntax::project(&doc, &sources, snapshot)
            .map_err(|e| fail(&source.uri, e.to_string()))?
        {
            ParseOutcome::Parsed(mut parsed) => {
                ast.declarations.append(&mut parsed.declarations);
                ast.mappings.append(&mut parsed.mappings);
                ast.masks.append(&mut parsed.masks);
            }
            ParseOutcome::SyntaxErrors(errors) => {
                return Err(errors
                    .into_iter()
                    .map(|e| Diagnostic {
                        uri: source.uri.clone(),
                        range: e.span.byte_range(),
                        message: e.message,
                    })
                    .collect());
            }
        }
    }
    let program = match lowering::lower(&ast, &sources)
        .map_err(|e| fail("inputmapping:assembly", e.to_string()))?
    {
        LoweringOutcome::Lowered(p) => p,
        LoweringOutcome::UserErrors(errors) => {
            return Err(errors
                .into_iter()
                .map(|e| Diagnostic {
                    uri: sources.snapshot(e.span.snapshot()).unwrap().uri.clone(),
                    range: e.span.byte_range(),
                    message: format!("{:?}", e.kind),
                })
                .collect());
        }
    };
    Ok(Assembled { sources, program })
}
/// File names are caller-owned layout choices, never IR namespaces or keys.
pub fn layout(
    program: &LoweredProgram,
    sources: &Sources,
    paths: &BTreeMap<SnapshotId, String>,
) -> std::result::Result<ExportLayout, ExportError> {
    let mut layout = ExportLayout {
        files: vec![ExportFile {
            path: "library/library.den".into(),
            ownership: Ownership::Library,
        }],
        placements: BTreeMap::new(),
    };
    let mut source_files = BTreeMap::new();
    let mut ordered = paths
        .iter()
        .map(|(id, path)| {
            Ok((
                sources
                    .snapshot(*id)
                    .map_err(|e| ExportError(e.to_string()))?
                    .uri
                    .clone(),
                *id,
                path,
            ))
        })
        .collect::<std::result::Result<Vec<_>, ExportError>>()?;
    ordered.sort();
    for (_, id, path) in ordered {
        source_files.insert(id, layout.files.len());
        layout.files.push(ExportFile {
            path: path.clone(),
            ownership: Ownership::User,
        });
    }
    let shared = if program
        .placements
        .values()
        .any(|p| *p == FilePlacement::Shared)
    {
        let i = layout.files.len();
        layout.files.push(ExportFile {
            path: "shared.den".into(),
            ownership: Ownership::User,
        });
        Some(i)
    } else {
        None
    };
    for (id, placement) in &program.placements {
        let file = match placement {
            FilePlacement::Library => 0,
            FilePlacement::Shared => shared.unwrap(),
            FilePlacement::Source(s) => *source_files
                .get(s)
                .ok_or_else(|| ExportError("Missing source file placement".into()))?,
        };
        layout.placements.insert(*id, file);
    }
    Ok(layout)
}
pub fn bundle(
    program: &LoweredProgram,
    sources: &Sources,
    paths: &BTreeMap<SnapshotId, String>,
    options: PrintOptions,
) -> std::result::Result<ExportBundle, ExportError> {
    print(
        &ExportProgram {
            corpus: &program.corpus,
            domains: &program.domains(),
            sources,
            provenance: &program.attribution.provenance,
            layout: &layout(program, sources, paths)?,
        },
        options,
    )
}
