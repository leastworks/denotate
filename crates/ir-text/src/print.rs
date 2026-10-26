//! Pure, deterministic export. Layout is supplied independently of namespace and origins.
use crate::{ProgramMembership, RootInfo, SourceFile, origins::*};
use denotate_check::Domains;
use denotate_ir::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    User,
    Library,
}
#[derive(Clone, Debug)]
pub struct ExportFile {
    pub path: String,
    pub ownership: Ownership,
}
#[derive(Clone, Debug, Default)]
pub struct ExportLayout {
    pub files: Vec<ExportFile>,
    pub placements: BTreeMap<OccurrenceId, usize>,
}
pub struct ExportProgram<'a> {
    pub corpus: &'a Corpus,
    pub domains: &'a Domains,
    pub sources: &'a Sources,
    pub provenance: &'a Provenance,
    pub layout: &'a ExportLayout,
}
#[derive(Clone, Copy, Debug)]
pub struct PrintOptions {
    pub embedded_origins: bool,
}
impl Default for PrintOptions {
    fn default() -> Self {
        Self {
            embedded_origins: true,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportError(pub String);
impl std::fmt::Display for ExportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ExportError {}
type Result<T> = std::result::Result<T, ExportError>;
fn fail(message: impl Into<String>) -> ExportError {
    ExportError(message.into())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportBundle {
    pub files: BTreeMap<String, String>,
}
impl ExportBundle {
    /// Supply this bundle directly to `load`, without disk or hidden discovery.
    pub fn documents(&self, base_uri: &str) -> (ProgramMembership, Vec<SourceFile>) {
        let uri = |p: &str| format!("{}/{p}", base_uri.trim_end_matches('/'));
        let mut roots = BTreeMap::from([(uri("den.root"), RootInfo::default())]);
        if self.files.contains_key("library/den.root") {
            roots.insert(uri("library/den.root"), RootInfo::default());
            roots
                .get_mut(&uri("den.root"))
                .unwrap()
                .libraries
                .insert(uri("library/den.root"));
        }
        let mut documents = Vec::new();
        for (path, text) in &self.files {
            if !path.ends_with(".den") {
                continue;
            }
            let root = if path.starts_with("library/") {
                "library/den.root"
            } else {
                "den.root"
            };
            roots.get_mut(&uri(root)).unwrap().files.insert(uri(path));
            documents.push(SourceFile::new(uri(path), 1, text.clone()));
        }
        (
            ProgramMembership {
                root: uri("den.root"),
                roots,
            },
            documents,
        )
    }
}
/// Escape a name when its bare spelling would change its identity or syntactic kind.
pub(crate) fn quote(s: &str) -> String {
    format!(
        "'{}'",
        s.replace('\\', "\\\\")
            .replace('\'', "\\'")
            .replace('\n', "\\n")
            .replace('\r', "\\r")
            .replace('\t', "\\t")
    )
}

#[derive(Clone, Copy)]
pub enum NameKind {
    Identifier,
    Constant,
    Parameter,
    Variable,
}
pub fn spelling(name: &str, kind: NameKind) -> String {
    let first = name.as_bytes().first().copied();
    let start = match kind {
        NameKind::Constant => first.is_some_and(|c| c.is_ascii_lowercase()),
        NameKind::Variable => first.is_some_and(|c| c.is_ascii_uppercase()),
        _ => first.is_some_and(|c| c.is_ascii_alphabetic()),
    };
    let identifier = start && name.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_');
    let reserved = !matches!(kind, NameKind::Parameter) && crate::reserved_word(name);
    let integer = matches!(kind, NameKind::Constant)
        && name
            .parse::<i64>()
            .is_ok_and(|value| value.to_string() == name);
    if (identifier && !reserved) || integer {
        name.into()
    } else if matches!(kind, NameKind::Variable) {
        format!("?{}", quote(name))
    } else {
        quote(name)
    }
}
fn namespace_text(namespace: &Namespace) -> String {
    namespace
        .segments()
        .iter()
        .map(|s| spelling(s, NameKind::Identifier))
        .collect::<Vec<_>>()
        .join("::")
}
#[derive(PartialEq, Eq)]
enum SymbolKind {
    Sort,
    Constant(SortId),
    Relation,
    Assumption,
    Obligation,
}
struct Symbol {
    text: String,
    kind: SymbolKind,
}
/// The printer emits no imports. Bare lookup sees all enclosing namespaces,
/// without shadowing; constant candidates additionally depend on the expected sort.
fn reference(
    c: &Corpus,
    symbols: &BTreeMap<OccurrenceId, Symbol>,
    id: OccurrenceId,
    context: &Namespace,
) -> String {
    let symbol = &symbols[&id];
    let namespace = c.namespace(id).unwrap();
    let visible = |id| {
        context
            .segments()
            .starts_with(c.namespace(id).unwrap().segments())
    };
    if visible(id)
        && symbols
            .iter()
            .filter(|(candidate, value)| {
                value.kind == symbol.kind && value.text == symbol.text && visible(**candidate)
            })
            .count()
            == 1
    {
        symbol.text.clone()
    } else {
        format!("{}::{}", namespace_text(namespace), symbol.text)
    }
}

/// Position vocabulary shared by printing and location attachment (not structural comparison).
pub(crate) fn rule_positions(rule: &Rule) -> BTreeMap<String, OccurrenceId> {
    let mut positions = BTreeMap::from([("self".into(), rule.id.into())]);
    for (prefix, atom) in std::iter::once(("head".into(), &rule.head)).chain(
        rule.body
            .iter()
            .enumerate()
            .map(|(i, l)| (format!("body.{i}"), l.atom())),
    ) {
        positions.insert(prefix.clone(), atom.id());
        for (i, t) in atom.arguments().iter().enumerate() {
            positions.insert(format!("{prefix}.{i}"), t.id());
        }
    }
    positions
}
fn validate(p: &ExportProgram<'_>) -> Result<()> {
    let top = top_level(p.corpus).into_iter().collect::<BTreeSet<_>>();
    if p.layout.placements.keys().copied().collect::<BTreeSet<_>>() != top {
        return Err(fail(
            "Layout must place every top-level occurrence exactly once, with no foreign or child IDs",
        ));
    }
    if p.layout
        .placements
        .values()
        .any(|i| *i >= p.layout.files.len())
    {
        return Err(fail("Unknown output file index"));
    }
    let mut paths = BTreeSet::new();
    for file in &p.layout.files {
        if !file.path.ends_with(".den")
            || file.path.contains('\\')
            || file
                .path
                .split('/')
                .any(|x| x.is_empty() || matches!(x, "." | ".." | "den.root"))
            || file.path.contains(':')
            || file.path.contains('\0')
        {
            return Err(fail(
                "Output paths must be relative .den paths without traversal",
            ));
        }
        if !paths.insert(&file.path) {
            return Err(fail("Duplicate output path"));
        }
        if file.path.starts_with("library/") != (file.ownership == Ownership::Library) {
            return Err(fail(
                "Library files must be under library/; user files must be outside it",
            ));
        }
    }
    for path in &paths {
        if paths
            .iter()
            .any(|other| other.starts_with(&format!("{path}/")))
        {
            return Err(fail("An output file cannot also be an output directory"));
        }
    }
    if p.domains.len() != p.corpus.sorts().count() {
        return Err(fail("Domains must cover exactly every sort"));
    }
    for sort in p.corpus.sorts() {
        let domain = p
            .domains
            .get(&sort.id)
            .ok_or_else(|| fail("Missing sort domain"))?;
        if domain.iter().collect::<BTreeSet<_>>().len() != domain.len() {
            return Err(fail("Duplicate domain member"));
        }
        if domain
            .iter()
            .any(|id| p.corpus.constant(*id).is_none_or(|c| c.sort != sort.id))
        {
            return Err(fail("Foreign or wrong-sort domain member"));
        }
    }
    for rule in p.corpus.rules() {
        for atom in std::iter::once(&rule.head).chain(rule.body.iter().map(Literal::atom)) {
            for term in atom.arguments() {
                if let Term::Constant(id) = term.value() {
                    let sort = p.corpus.constant(*id).unwrap().sort;
                    if !p.domains[&sort].contains(id) {
                        return Err(fail("Rule uses a constant outside its domain"));
                    }
                }
            }
        }
    }
    for (id, origins) in p.provenance.entries() {
        if !p.corpus.contains_occurrence(id) {
            return Err(fail("Foreign provenance occurrence"));
        }
        for origin in origins {
            p.sources
                .text(origin.span)
                .map_err(|e| fail(e.to_string()))?;
        }
    }
    Ok(())
}
struct Line {
    block: bool,
    namespace: Namespace,
    text: String,
    origins: BTreeMap<String, Vec<OriginDescriptor>>,
}
fn descriptors(sources: &Sources, origins: &[Origin]) -> Result<Vec<OriginDescriptor>> {
    let values = origins
        .iter()
        .map(|o| OriginDescriptor::of(sources, o).map_err(|e| fail(e.to_string())))
        .collect::<Result<BTreeSet<_>>>()?;
    Ok(values.into_iter().collect())
}
fn helper_label(name: &str) -> bool {
    name.strip_prefix('$').is_some_and(|name| {
        name.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
            && name.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_')
    })
}
fn position_order(position: &str) -> (u8, Vec<usize>) {
    let mut parts = position.split('.');
    let kind = match parts.next().unwrap() {
        "self" => 0,
        "head" => 1,
        "body" => 2,
        "decl" => 3,
        _ => unreachable!("printer-created occurrence position"),
    };
    (
        kind,
        parts
            .map(|p| p.parse().expect("printer-created occurrence index"))
            .collect(),
    )
}
pub fn print(p: &ExportProgram<'_>, options: PrintOptions) -> Result<ExportBundle> {
    validate(p)?;
    let c = p.corpus;
    let mut symbols = BTreeMap::<OccurrenceId, Symbol>::new();
    for s in c.sorts() {
        symbols.insert(
            s.id.into(),
            Symbol {
                text: spelling(&s.name, NameKind::Identifier),
                kind: SymbolKind::Sort,
            },
        );
    }
    for k in c.constants() {
        symbols.insert(
            k.id.into(),
            Symbol {
                text: spelling(&k.name, NameKind::Constant),
                kind: SymbolKind::Constant(k.sort),
            },
        );
    }
    // Reserve every legal authored helper label before allocating replacements,
    // so an earlier invalid/duplicate label cannot steal a later valid one.
    let mut used = c
        .relations()
        .filter(|r| c.is_generated_relation(r.id) && helper_label(&r.name))
        .map(|r| (c.namespace(r.id).unwrap().clone(), r.name.clone()))
        .collect::<BTreeSet<_>>();
    let mut preserved = BTreeSet::new();
    for r in c.relations() {
        let ns = c.namespace(r.id).unwrap();
        let name = if c.is_generated_relation(r.id) {
            if helper_label(&r.name) && preserved.insert((ns.clone(), r.name.clone())) {
                r.name.clone()
            } else {
                let mut index = 1;
                loop {
                    let label = format!("$condition_{index}");
                    if used.insert((ns.clone(), label.clone())) {
                        break label;
                    }
                    index += 1;
                }
            }
        } else {
            spelling(&r.name, NameKind::Identifier)
        };
        symbols.insert(
            r.id.into(),
            Symbol {
                text: name,
                kind: SymbolKind::Relation,
            },
        );
    }
    for a in c.assumptions() {
        symbols.insert(
            a.id.into(),
            Symbol {
                text: spelling(&a.name, NameKind::Identifier),
                kind: SymbolKind::Assumption,
            },
        );
    }
    for o in c.obligations() {
        symbols.insert(
            o.id.into(),
            Symbol {
                text: spelling(&o.name, NameKind::Identifier),
                kind: SymbolKind::Obligation,
            },
        );
    }
    let reference = |id, context: &Namespace| reference(c, &symbols, id, context);
    let mut lines: Vec<Vec<Line>> = p.layout.files.iter().map(|_| Vec::new()).collect();
    let mut add =
        |id: OccurrenceId, text: String, positions: BTreeMap<String, OccurrenceId>| -> Result<()> {
            let origins = if options.embedded_origins {
                positions
                    .into_iter()
                    .map(|(key, id)| Ok((key, descriptors(p.sources, p.provenance.origins(id))?)))
                    .collect::<Result<_>>()?
            } else {
                BTreeMap::new()
            };
            lines[p.layout.placements[&id]].push(Line {
                block: c.verifications().any(|v| OccurrenceId::from(v.id) == id),
                namespace: c.namespace(id).unwrap().clone(),
                text,
                origins,
            });
            Ok(())
        };
    let single = |id| BTreeMap::from([("self".into(), id)]);
    for s in c.sorts() {
        add(
            s.id.into(),
            format!("sort {}", symbols[&s.id.into()].text),
            single(s.id.into()),
        )?;
    }
    for k in c.constants() {
        add(
            k.id.into(),
            format!(
                "const {}: {}",
                symbols[&k.id.into()].text,
                reference(k.sort.into(), c.namespace(k.id).unwrap())
            ),
            single(k.id.into()),
        )?;
    }
    for r in c.relations() {
        let params = r
            .parameters
            .iter()
            .map(|p| {
                format!(
                    "{}: {}",
                    spelling(&p.name, NameKind::Parameter),
                    reference(p.sort.into(), c.namespace(r.id).unwrap())
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        add(
            r.id.into(),
            format!(
                "{} {}({params})",
                if r.role == RelationRole::Input {
                    "input"
                } else {
                    "relation"
                },
                symbols[&r.id.into()].text
            ),
            single(r.id.into()),
        )?;
    }
    let atom = |a: &Atom, context: &Namespace| {
        let terms = a
            .arguments()
            .iter()
            .map(|t| match t.value() {
                Term::Constant(id) => reference((*id).into(), context),
                Term::Variable { name, .. } => spelling(name, NameKind::Variable),
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("{}({terms})", reference(a.relation().into(), context))
    };
    for r in c.rules() {
        let context = c.namespace(r.id).unwrap();
        let mut text = atom(&r.head, context);
        if !r.body.is_empty() {
            text.push_str(" :- ");
            text.push_str(
                &r.body
                    .iter()
                    .map(|l| {
                        format!(
                            "{}{}",
                            if matches!(l, Literal::Negative(_)) {
                                "!"
                            } else {
                                ""
                            },
                            atom(l.atom(), context)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }
        add(r.id.into(), text, rule_positions(r))?;
    }
    let contract = |kind: &str, relation: RelationId, columns: &[usize], context: &Namespace| {
        format!(
            "{kind}({}, group_by: ({}))",
            reference(relation.into(), context),
            columns
                .iter()
                .map(|i| spelling(
                    &c.relation(relation).unwrap().parameters[*i].name,
                    NameKind::Parameter
                ))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    for o in c.obligations() {
        let relation = &o.requirement.relation();
        let group_by = o.requirement.group_by();
        let kind = match o.requirement {
            Requirement::AtMostOne { .. } => "at_most_one",
            Requirement::AtLeastOne { .. } => "at_least_one",
        };
        add(
            o.id.into(),
            format!(
                "obligation {}: {} message {}",
                spelling(&o.name, NameKind::Identifier),
                contract(kind, *relation, group_by, c.namespace(o.id).unwrap()),
                serde_json::to_string(&o.message_template).unwrap()
            ),
            single(o.id.into()),
        )?;
    }
    for a in c.assumptions() {
        let Restriction::AtMostOne { relation, group_by } = &a.restriction;
        add(
            a.id.into(),
            format!(
                "assumption {}: {}",
                spelling(&a.name, NameKind::Identifier),
                contract(
                    "at_most_one",
                    *relation,
                    group_by,
                    c.namespace(a.id).unwrap()
                )
            ),
            single(a.id.into()),
        )?;
    }
    for v in c.verifications() {
        let context = c.namespace(v.id).unwrap();
        let assumptions = v
            .assumptions
            .iter()
            .map(|id| reference((*id).into(), context))
            .collect::<Vec<_>>()
            .join(", ");
        let obligations = v
            .obligations
            .iter()
            .map(|id| reference((*id).into(), context))
            .collect::<Vec<_>>()
            .join(", ");
        add(
            v.id.into(),
            format!(
                "verification {} {{ assumptions: [{assumptions}]; obligations: [{obligations}]; }}",
                spelling(&v.name, NameKind::Identifier)
            ),
            single(v.id.into()),
        )?;
    }
    for s in c.sorts() {
        let defaults = c
            .constants()
            .filter(|k| k.sort == s.id)
            .map(|k| k.id)
            .collect::<BTreeSet<_>>();
        if p.domains[&s.id].iter().copied().collect::<BTreeSet<_>>() != defaults {
            let mut members = p.domains[&s.id]
                .iter()
                .map(|id| reference((*id).into(), c.namespace(s.id).unwrap()))
                .collect::<Vec<_>>();
            members.sort();
            lines[p.layout.placements[&s.id.into()]].push(Line {
                block: false,
                namespace: c.namespace(s.id).unwrap().clone(),
                text: format!(
                    "domain {} = [{}]",
                    reference(s.id.into(), c.namespace(s.id).unwrap()),
                    members.join(", ")
                ),
                origins: BTreeMap::new(),
            });
        }
    }
    let mut files = BTreeMap::new();
    for (file, lines) in p.layout.files.iter().zip(lines) {
        files.insert(file.path.clone(), render(lines));
    }
    let library = p
        .layout
        .files
        .iter()
        .any(|f| f.ownership == Ownership::Library);
    files.insert(
        "den.root".into(),
        if library {
            "{\"libraries\":[\"library/den.root\"]}\n"
        } else {
            "{}\n"
        }
        .into(),
    );
    if library {
        files.insert("library/den.root".into(), "{}\n".into());
    }
    Ok(ExportBundle { files })
}
fn range(o: &OriginDescriptor) -> String {
    format!(
        "{}:{} to {}:{}",
        o.start.line, o.start.column, o.end.line, o.end.column
    )
}
fn render(lines: Vec<Line>) -> String {
    let identities = lines
        .iter()
        .flat_map(|l| l.origins.values().flatten().map(|o| o.source.clone()))
        .collect::<BTreeSet<_>>();
    let sources = identities
        .into_iter()
        .enumerate()
        .map(|(i, s)| (s, format!("#src{i}")))
        .collect::<BTreeMap<_, _>>();
    let scalar = |origins: &[OriginDescriptor]| {
        let values = origins
            .iter()
            .map(|o| format!("{} {}", sources[&o.source], range(o)))
            .collect::<Vec<_>>();
        if values.len() == 1 {
            format!("loc({})", values[0])
        } else {
            format!("loc(fused[{}])", values.join(", "))
        }
    };
    let namespaces = lines
        .iter()
        .map(|l| l.namespace.clone())
        .collect::<BTreeSet<_>>();
    let file_scoped = namespaces.len() == 1 && !namespaces.first().unwrap().is_global();
    let mut out = String::new();
    if file_scoped {
        out.push_str(&format!(
            "namespace {};\n\n",
            namespace_text(namespaces.first().unwrap())
        ));
    }
    let mut aliases = Vec::new();
    let mut open_namespace = Namespace::default();
    for mut line in lines {
        line.origins.retain(|_, v| !v.is_empty());
        let suffix = if line.origins.is_empty() {
            String::new()
        } else if line.origins.len() == 1 && line.origins.contains_key("self") {
            format!(" {}", scalar(&line.origins["self"]))
        } else {
            let alias = format!("#origin{}", aliases.len());
            let first = &line.origins.values().next().unwrap()[0].source;
            let compact = line
                .origins
                .values()
                .all(|v| v.len() == 1 && &v[0].source == first);
            let mut positions = line.origins.iter().collect::<Vec<_>>();
            positions.sort_by_key(|(position, _)| position_order(position));
            let value = if compact {
                format!(
                    "loc({} {{ {} }})",
                    sources[first],
                    positions
                        .iter()
                        .map(|(pos, v)| format!("{pos}: {}", range(&v[0])))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                format!(
                    "{{ {} }}",
                    positions
                        .iter()
                        .map(|(pos, v)| format!("{pos}: {}", scalar(v)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            aliases.push(format!("{alias} = {value};\n"));
            format!(" loc({alias})")
        };
        let terminator = if line.block { "" } else { ";" };
        let declaration = format!("{}{suffix}{terminator}\n", line.text);
        if !file_scoped && open_namespace != line.namespace {
            if !open_namespace.is_global() {
                out.push_str("}\n");
            }
            if !line.namespace.is_global() {
                out.push_str(&format!(
                    "namespace {} {{\n",
                    namespace_text(&line.namespace)
                ));
            }
            open_namespace = line.namespace;
        }
        if !file_scoped && !open_namespace.is_global() {
            out.push_str("  ");
        }
        out.push_str(&declaration);
    }
    if !open_namespace.is_global() {
        out.push_str("}\n");
    }
    if !sources.is_empty() {
        out.push('\n');
    }
    for (s, alias) in sources {
        out.push_str(&format!(
            "{alias} = source({}, view: {}, hash: {});\n",
            serde_json::to_string(&s.uri).unwrap(),
            serde_json::to_string(&s.view).unwrap(),
            serde_json::to_string(&s.hash).unwrap()
        ));
    }
    for alias in aliases {
        out.push_str(&alias);
    }
    out
}
