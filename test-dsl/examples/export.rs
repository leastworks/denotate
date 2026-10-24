//! Export one combined InputMapping program to a new/empty output directory.
use denotate_ir_text::{PrintOptions, SourceFile, filesystem::uri};
use denotate_test_dsl::export;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let output = PathBuf::from(
        args.next()
            .ok_or("Usage: export OUT_DIR FILE... [--without-origins]")?,
    );
    let mut options = PrintOptions::default();
    let mut inputs = BTreeSet::new();
    for arg in args {
        if arg == "--without-origins" {
            options.embedded_origins = false;
            continue;
        }
        let path = std::fs::canonicalize(&arg).map_err(|e| format!("{arg}: {e}"))?;
        if !inputs.insert(path) {
            return Err(format!("Repeated canonical input file: {arg}"));
        }
    }
    if inputs.is_empty() {
        return Err("At least one input file is required".into());
    }
    if output.exists()
        && (!output.is_dir()
            || std::fs::read_dir(&output)
                .map_err(|e| e.to_string())?
                .next()
                .is_some())
    {
        return Err("Output destination must be a new or empty directory".into());
    }
    let documents = inputs
        .iter()
        .map(|path| {
            Ok(SourceFile::new(
                uri(path),
                1,
                std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?,
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let assembled = export::assemble(&documents).map_err(|ds| {
        ds.iter()
            .map(|d| {
                format!(
                    "{}:{}..{}: {}",
                    d.uri, d.range.start, d.range.end, d.message
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let mut ancestor = inputs.first().unwrap().parent().unwrap();
    while !inputs.iter().all(|path| path.starts_with(ancestor)) {
        ancestor = ancestor.parent().ok_or("Inputs have no common ancestor")?;
    }
    let mut used = BTreeSet::new();
    let mut paths = BTreeMap::new();
    // URI ordering agrees with assembly, independently of argument/registration order.
    let mut ordered = inputs
        .iter()
        .map(|path| (uri(path), path))
        .collect::<Vec<_>>();
    ordered.sort();
    for (source, path) in ordered {
        let relative = path.strip_prefix(ancestor).unwrap().with_extension("den");
        let mut name = Path::new("sources")
            .join(&relative)
            .to_string_lossy()
            .into_owned();
        let mut suffix = 1;
        while !used.insert(name.clone()) {
            let stem = relative.file_stem().unwrap().to_string_lossy();
            let unique = relative.with_file_name(format!("{stem}-{suffix}.den"));
            name = Path::new("sources")
                .join(unique)
                .to_string_lossy()
                .into_owned();
            suffix += 1;
        }
        let snapshot = assembled
            .sources
            .snapshots()
            .find(|s| s.uri == source)
            .unwrap();
        paths.insert(snapshot.id, name);
    }
    let bundle = export::bundle(&assembled.program, &assembled.sources, &paths, options)
        .map_err(|e| e.to_string())?;
    // All parsing, lowering and export validation has succeeded before writing.
    for (path, text) in &bundle.files {
        let path = output.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).map_err(|e| e.to_string())?;
        std::fs::write(path, text).map_err(|e| e.to_string())?;
    }
    for (id, path) in paths {
        println!(
            "{} -> {}",
            assembled.sources.snapshot(id).unwrap().uri,
            output.join(path).display()
        );
    }
    println!("Root: {}", output.join("den.root").display());
    println!(
        "Check: just check-den '{}'",
        output.display().to_string().replace('\'', "'\\''")
    );
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
