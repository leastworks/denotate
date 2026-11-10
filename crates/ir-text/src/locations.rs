//! File-local location graphs. Validate first; only then restore source associations.
use crate::{
    Diagnostic, LoadedProgram, Result, SourceFile, error, origins::*, parser, print::rule_positions,
};
use denotate_ir::*;
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};
use tree_sitter::Node;

#[derive(Clone)]
enum Value {
    Source(SourceIdentity),
    Alias(String),
    Range(String, Coordinate, Coordinate),
    Compact(String, Box<Value>),
    Fused(Vec<Value>),
    Map(BTreeMap<String, Value>),
    Location(Box<Value>),
}
#[derive(Clone)]
enum Resolved {
    Source(SourceIdentity),
    Origins(Vec<OriginDescriptor>),
    Map(BTreeMap<String, Vec<OriginDescriptor>>),
}
fn children(n: Node<'_>) -> Vec<Node<'_>> {
    n.named_children(&mut n.walk())
        .filter(|n| n.kind() != "comment")
        .collect()
}
fn field<'a>(n: Node<'a>, name: &str) -> Node<'a> {
    n.child_by_field_name(name)
        .expect("checked location grammar")
}
fn text<'a>(s: &'a SourceFile, n: Node<'_>) -> &'a str {
    &s.text[n.byte_range()]
}
fn json(s: &SourceFile, n: Node<'_>) -> Result<String> {
    serde_json::from_str(text(s, n)).map_err(|e| error(s, n.byte_range(), e.to_string()))
}
fn coord(s: &SourceFile, n: Node<'_>) -> Result<Coordinate> {
    let number = |key| {
        text(s, field(n, key))
            .parse::<usize>()
            .ok()
            .filter(|v| *v > 0)
            .ok_or_else(|| {
                error(
                    s,
                    n.byte_range(),
                    "Coordinates must be positive machine-sized integers",
                )
            })
    };
    Ok(Coordinate {
        line: number("line")?,
        column: number("column")?,
    })
}
fn range(s: &SourceFile, n: Node<'_>, source: String) -> Result<Value> {
    let start = coord(s, field(n, "start"))?;
    let end = coord(s, field(n, "end"))?;
    if start > end {
        return Err(error(s, n.byte_range(), "Reversed source range"));
    }
    Ok(Value::Range(source, start, end))
}
fn position(s: &SourceFile, n: Node<'_>) -> Result<String> {
    let raw = text(s, n);
    let parts = raw.split('.').collect::<Vec<_>>();
    let valid = matches!(
        parts.as_slice(),
        ["self"] | ["head"] | ["head", _] | ["body", _] | ["body", _, _] | ["decl", _]
    );
    if !valid {
        return Err(error(s, n.byte_range(), "Invalid occurrence position"));
    }
    let mut out = vec![parts[0].to_owned()];
    for part in &parts[1..] {
        out.push(
            part.parse::<usize>()
                .map_err(|_| error(s, n.byte_range(), "Invalid occurrence index"))?
                .to_string(),
        );
    }
    Ok(out.join("."))
}
fn value(s: &SourceFile, n: Node<'_>) -> Result<Value> {
    let cs = children(n);
    Ok(match n.kind() {
        "source_location" => {
            let identity = SourceIdentity {
                uri: json(s, field(n, "uri"))?,
                view: json(s, field(n, "view"))?,
                hash: json(s, field(n, "hash"))?,
            };
            if identity.uri.is_empty()
                || identity.view.is_empty()
                || identity.hash.len() != 71
                || !identity.hash.starts_with("sha256:")
                || !identity.hash[7..]
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return Err(error(
                    s,
                    n.byte_range(),
                    "Expected nonempty URI/view and a lowercase sha256: digest",
                ));
            }
            Value::Source(identity)
        }
        "alias" => Value::Alias(text(s, n).into()),
        "location" => Value::Location(Box::new(value(s, cs[0])?)),
        "location_value" => {
            if cs.len() == 1 && !text(s, n).starts_with("fused") {
                value(s, cs[0])?
            } else {
                Value::Fused(cs.into_iter().map(|n| value(s, n)).collect::<Result<_>>()?)
            }
        }
        "source_range" => range(s, cs[1], text(s, field(n, "source")).into())?,
        "occurrence_map" | "compact_map" => {
            let mut entries = BTreeMap::new();
            for entry in cs
                .into_iter()
                .filter(|n| matches!(n.kind(), "location_entry" | "compact_entry"))
            {
                let key = position(s, field(entry, "position"))?;
                let v = children(entry)
                    .into_iter()
                    .find(|n| matches!(n.kind(), "location" | "coordinate_range"))
                    .unwrap();
                let v = if n.kind() == "compact_map" {
                    range(s, v, text(s, field(n, "source")).into())?
                } else {
                    value(s, v)?
                };
                if entries.insert(key, v).is_some() {
                    return Err(error(
                        s,
                        entry.byte_range(),
                        "Duplicate occurrence position",
                    ));
                }
            }
            let map = Value::Map(entries);
            if n.kind() == "compact_map" {
                Value::Compact(text(s, field(n, "source")).into(), Box::new(map))
            } else {
                map
            }
        }
        _ => return Err(error(s, n.byte_range(), "Invalid location expression")),
    })
}
struct Graph<'a> {
    source: &'a SourceFile,
    definitions: BTreeMap<String, (Value, Range<usize>)>,
    resolved: BTreeMap<String, Resolved>,
    visiting: BTreeSet<String>,
}
impl Graph<'_> {
    fn alias(&mut self, name: &str, span: Range<usize>) -> Result<Resolved> {
        if let Some(v) = self.resolved.get(name) {
            return Ok(v.clone());
        }
        if !self.visiting.insert(name.into()) {
            return Err(error(self.source, span, "Cyclic location alias"));
        }
        let (v, at) = self.definitions.get(name).cloned().ok_or_else(|| {
            error(
                self.source,
                span,
                format!("Undefined location alias {name}"),
            )
        })?;
        let resolved = self.eval(&v, at)?;
        self.visiting.remove(name);
        self.resolved.insert(name.into(), resolved.clone());
        Ok(resolved)
    }
    fn eval(&mut self, v: &Value, span: Range<usize>) -> Result<Resolved> {
        let wrong = || {
            error(
                self.source,
                span.clone(),
                "Wrong-kind location reference (sources, scalar locations and occurrence maps are distinct)",
            )
        };
        Ok(match v {
            Value::Source(s) => Resolved::Source(s.clone()),
            Value::Alias(a) => self.alias(a, span)?,
            Value::Location(v) => match self.eval(v, span.clone())? {
                Resolved::Source(_) => return Err(wrong()),
                r => r,
            },
            Value::Range(a, start, end) => {
                let Resolved::Source(source) = self.alias(a, span.clone())? else {
                    return Err(wrong());
                };
                Resolved::Origins(vec![OriginDescriptor {
                    source,
                    start: *start,
                    end: *end,
                }])
            }
            Value::Compact(source, map) => {
                if !matches!(self.alias(source, span.clone())?, Resolved::Source(_)) {
                    return Err(wrong());
                }
                self.eval(map, span)?
            }
            Value::Fused(vs) => {
                let mut origins = BTreeSet::new();
                for v in vs {
                    let Resolved::Origins(values) = self.eval(v, span.clone())? else {
                        return Err(wrong());
                    };
                    origins.extend(values);
                }
                if origins.is_empty() {
                    return Err(error(self.source, span, "Fused locations must be nonempty"));
                }
                Resolved::Origins(origins.into_iter().collect())
            }
            Value::Map(vs) => {
                let mut entries = BTreeMap::new();
                for (k, v) in vs {
                    let Resolved::Origins(values) = self.eval(v, span.clone())? else {
                        return Err(wrong());
                    };
                    entries.insert(k.clone(), values);
                }
                Resolved::Map(entries)
            }
        })
    }
}
fn collect<'a>(n: Node<'a>, aliases: &mut Vec<Node<'a>>, suffixes: &mut Vec<(Node<'a>, Node<'a>)>) {
    if matches!(n.kind(), "source_location" | "location_alias") {
        aliases.push(n);
        return;
    }
    if matches!(
        n.kind(),
        "sort"
            | "constants"
            | "relation"
            | "statement"
            | "obligation"
            | "assumption"
            | "verification"
            | "notice"
    ) {
        if let Some(loc) = children(n).into_iter().find(|c| c.kind() == "location") {
            suffixes.push((n, loc));
        }
        return;
    }
    for child in children(n) {
        collect(child, aliases, suffixes);
    }
}
/// Current-text top-level spans, indexed once for this load. Range lookup only
/// visits occurrences that start inside the annotated statement; unrelated files
/// and earlier/later statements are excluded before inspecting provenance.
struct RangeIndex<T> {
    documents: BTreeMap<String, Vec<(Range<usize>, T)>>,
}
impl<T: Copy + Into<OccurrenceId>> RangeIndex<T> {
    fn new(p: &LoadedProgram, ids: impl IntoIterator<Item = T>) -> Self {
        let mut documents = BTreeMap::<String, Vec<(Range<usize>, T)>>::new();
        for id in ids {
            if let Some(origin) = p.provenance.origins(id.into()).first() {
                let snapshot = p.sources.snapshot(origin.span.snapshot()).unwrap();
                documents
                    .entry(snapshot.uri.clone())
                    .or_default()
                    .push((origin.span.byte_range(), id));
            }
        }
        for entries in documents.values_mut() {
            // Stable sort preserves corpus order for coincident starts, including
            // grouped declarations. Only the first current origin is authoritative.
            entries.sort_by_key(|(range, _)| range.start);
        }
        Self { documents }
    }
    fn within(&self, uri: &str, range: Range<usize>) -> impl Iterator<Item = T> + '_ {
        let entries = self.documents.get(uri).map(Vec::as_slice).unwrap_or(&[]);
        let start = entries.partition_point(|(r, _)| r.start < range.start);
        entries[start..]
            .iter()
            .take_while(move |(r, _)| r.start <= range.end)
            .filter(move |(r, _)| r.end <= range.end)
            .map(|(_, id)| *id)
    }
}
struct TargetIndex {
    declarations: RangeIndex<OccurrenceId>,
    rules: RangeIndex<RuleId>,
}
impl TargetIndex {
    fn new(p: &LoadedProgram) -> Self {
        Self {
            declarations: RangeIndex::new(p, top_level(&p.corpus)),
            rules: RangeIndex::new(p, p.corpus.rules().map(|r| r.id)),
        }
    }
    fn positions(
        &self,
        p: &LoadedProgram,
        source: &SourceFile,
        statement: Node<'_>,
    ) -> BTreeMap<String, Vec<OriginTarget>> {
        let mut result = BTreeMap::new();
        let range = statement.byte_range();
        if statement.kind() == "statement" {
            // Rule IDs follow corpus iteration order, preserving the old first
            // match even if several rules ever share a current-text span.
            if let Some(id) = self.rules.within(&source.uri, range).min() {
                return rule_positions(p.corpus.rule(id).unwrap())
                    .into_iter()
                    .map(|(pos, id)| (pos, vec![OriginTarget::Occurrence(id)]))
                    .collect();
            }
        } else {
            let ids = self
                .declarations
                .within(&source.uri, range)
                .collect::<Vec<_>>();
            if statement.kind() == "constants" {
                for (i, id) in ids.iter().enumerate() {
                    result.insert(format!("decl.{i}"), vec![OriginTarget::Occurrence(*id)]);
                }
            }
            result.insert(
                "self".into(),
                ids.into_iter().map(OriginTarget::Occurrence).collect(),
            );
        }
        result
    }
}
fn descriptors(r: &Resolved) -> Vec<OriginDescriptor> {
    match r {
        Resolved::Source(_) => vec![],
        Resolved::Origins(v) => v.clone(),
        Resolved::Map(m) => m.values().flatten().cloned().collect(),
    }
}
/// `provenance` remains the current-text view. Restored links have their own table,
/// even when both view names are `denotate`.
pub(crate) fn restore(
    p: &mut LoadedProgram,
    documents: &[SourceFile],
    mut resolver: Option<&mut dyn OriginResolver>,
) -> Result<()> {
    let mut references = BTreeMap::<OriginDescriptor, (String, Range<usize>)>::new();
    let mut identities = BTreeSet::new();
    let mut associations = BTreeMap::<OriginTarget, BTreeSet<OriginDescriptor>>::new();
    let members = p.membership.members()?;
    let mut targets = None;
    for doc in documents.iter().filter(|d| members.contains_key(&d.uri)) {
        let tree = parser().parse(doc.text.as_ref(), None).unwrap();
        let (mut aliases, mut suffixes) = (Vec::new(), Vec::new());
        collect(tree.root_node(), &mut aliases, &mut suffixes);
        let mut graph = Graph {
            source: doc,
            definitions: BTreeMap::new(),
            resolved: BTreeMap::new(),
            visiting: BTreeSet::new(),
        };
        for n in aliases {
            let name = text(doc, field(n, "name")).to_owned();
            let v = if n.kind() == "source_location" {
                value(doc, n)?
            } else {
                value(doc, *children(n).last().unwrap())?
            };
            if graph
                .definitions
                .insert(name, (v, n.byte_range()))
                .is_some()
            {
                return Err(error(doc, n.byte_range(), "Duplicate location alias"));
            }
        }
        for name in graph.definitions.keys().cloned().collect::<Vec<_>>() {
            let span = graph.definitions[&name].1.clone();
            let r = graph.alias(&name, span.clone())?;
            if let Resolved::Source(s) = &r {
                identities.insert(s.clone());
            }
            for d in descriptors(&r) {
                identities.insert(d.source.clone());
                references.insert(d, (doc.uri.clone(), span.clone()));
            }
        }
        for (statement, n) in suffixes {
            let v = value(doc, n)?;
            let r = graph.eval(&v, n.byte_range())?;
            let entries = match r {
                Resolved::Origins(v) => BTreeMap::from([("self".into(), v)]),
                Resolved::Map(m) => m,
                Resolved::Source(_) => {
                    return Err(error(doc, n.byte_range(), "A source is not a location"));
                }
            };
            let positions = targets
                .get_or_insert_with(|| TargetIndex::new(p))
                .positions(p, doc, statement);
            for (pos, origins) in entries {
                let targets = positions
                    .get(&pos)
                    .filter(|ids| !ids.is_empty())
                    .ok_or_else(|| {
                        error(
                            doc,
                            n.byte_range(),
                            format!("Nonexistent occurrence position {pos}"),
                        )
                    })?;
                for origin in &origins {
                    identities.insert(origin.source.clone());
                    references.insert(origin.clone(), (doc.uri.clone(), n.byte_range()));
                }
                for target in targets {
                    associations
                        .entry(target.clone())
                        .or_default()
                        .extend(origins.iter().cloned());
                }
            }
        }
    }
    // Resolve once per identity and reserve revisions independently of source IDs.
    let mut snapshots = BTreeMap::new();
    let mut notices = Vec::new();
    for identity in identities {
        let resolution = match resolver.as_deref_mut() {
            Some(r) => r.resolve(&identity),
            None => Err(Unavailable::NoResolver),
        };
        match resolution {
            Ok(text) if content_hash(&text) == identity.hash => {
                let mut revision = 0;
                while p
                    .sources
                    .snapshots()
                    .any(|s| s.uri == identity.uri && s.revision == revision)
                {
                    revision += 1;
                }
                let id = p
                    .sources
                    .add(&identity.uri, revision, &identity.view, text)
                    .map_err(|e| {
                        vec![Diagnostic {
                            uri: identity.uri.clone(),
                            range: 0..0,
                            message: e.to_string(),
                        }]
                    })?;
                snapshots.insert(identity, id);
            }
            other => notices.push(OriginNotice {
                source: identity,
                reason: other.err().unwrap_or(Unavailable::HashMismatch),
            }),
        }
    }
    let mut spans = BTreeMap::new();
    // Descriptors sort by source identity first. Batch one source's endpoints so
    // overlapping ranges and repeated coordinates never rescan its text.
    let mut references = references.into_iter().peekable();
    while let Some(first) = references.next() {
        let source = first.0.source.clone();
        let mut group = vec![first];
        while references.peek().is_some_and(|(d, _)| d.source == source) {
            group.push(references.next().unwrap());
        }
        if let Some(id) = snapshots.get(&source) {
            let text = &p.sources.snapshot(*id).unwrap().text;
            let offsets = byte_offsets(text, group.iter().flat_map(|(d, _)| [d.start, d.end]));
            for (descriptor, (uri, range)) in group {
                let span = offsets
                    .get(&descriptor.start)
                    .zip(offsets.get(&descriptor.end))
                    .and_then(|(a, b)| p.sources.span(*id, *a..*b).ok())
                    .ok_or_else(|| {
                        vec![Diagnostic {
                            uri,
                            range,
                            message: "Invalid coordinates in matching source snapshot".into(),
                        }]
                    })?;
                spans.insert(descriptor, span);
            }
        }
    }
    let mut embedded = EmbeddedOrigins {
        notices,
        ..Default::default()
    };
    for (target, descriptors) in associations {
        let origins = descriptors
            .iter()
            .filter_map(|d| spans.get(d))
            .map(|s| Origin::new(*s))
            .collect::<Vec<_>>();
        if !origins.is_empty() {
            match target {
                OriginTarget::Occurrence(id) => embedded
                    .provenance
                    .attach(&p.corpus, &p.sources, id, origins)
                    .expect("validated location graph"),
            }
        }
        embedded
            .associations
            .insert(target, descriptors.into_iter().collect());
    }
    p.embedded = embedded;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deliberately independent, slow reference for target selection. The release
    /// benchmark exercises scaling; this oracle checks range/index equivalence.
    fn scanned_positions(
        p: &LoadedProgram,
        doc: &SourceFile,
        statement: Node<'_>,
    ) -> BTreeMap<String, Vec<OriginTarget>> {
        let within = |id: OccurrenceId| {
            p.provenance.origins(id).first().is_some_and(|o| {
                let snapshot = p.sources.snapshot(o.span.snapshot()).unwrap();
                let range = o.span.byte_range();
                snapshot.uri == doc.uri
                    && statement.start_byte() <= range.start
                    && range.end <= statement.end_byte()
            })
        };
        if statement.kind() == "statement" {
            return p
                .corpus
                .rules()
                .find(|r| within(r.id.into()))
                .map(|r| {
                    rule_positions(r)
                        .into_iter()
                        .map(|(pos, id)| (pos, vec![OriginTarget::Occurrence(id)]))
                        .collect()
                })
                .unwrap_or_default();
        }
        let mut ids = top_level(&p.corpus)
            .into_iter()
            .filter(|id| within(*id))
            .collect::<Vec<_>>();
        ids.sort_by_key(|id| p.provenance.origins(*id)[0].span.byte_range().start);
        let mut positions = BTreeMap::new();
        if statement.kind() == "constants" {
            for (i, id) in ids.iter().enumerate() {
                positions.insert(format!("decl.{i}"), vec![OriginTarget::Occurrence(*id)]);
            }
        }
        positions.insert(
            "self".into(),
            ids.into_iter().map(OriginTarget::Occurrence).collect(),
        );
        positions
    }

    #[test]
    fn indexed_targets_match_scans_across_files_namespaces_and_occurrence_maps() {
        let docs = (0..12).map(|file| SourceFile::new(
            format!("file:///doc-{file:02}.den"), 7,
            format!(r#"
                namespace n{file:02} {{
                    sort S loc(#s 1:1 to 1:4);
                    const a, b: S loc(#s {{self: 1:1 to 1:4, decl.1: 1:2 to 1:3}});
                    input i(x:S) loc(#s 1:1 to 1:4);
                    relation p(x:S) loc(#s 1:1 to 1:4);
                    p(a) loc(#s {{self: 1:1 to 1:4, head: 1:1 to 1:4, head.0: 1:2 to 1:3}});
                    p(X) :- i(X) loc(#s {{self: 1:1 to 1:4, body.0: 1:1 to 1:4, body.0.0: 1:2 to 1:3}});
                    obligation unique: at_most_one(p, group_by: ()) loc(#s 1:1 to 1:4);
                    assumption single: at_most_one(i, group_by: ()) loc(#s 1:1 to 1:4);
                    input condition() loc(#s 1:1 to 1:4);
                    notice inspect: varies(condition) loc(#s 1:1 to 1:4);
                    verification checks {{ assumptions: [single]; obligations: [unique]; notices: [inspect]; }} loc(#s 1:1 to 1:4)
                }}
                #s = source("file:///source-{file:02}.dsl", view: "dsl", hash: "{}");
            "#, content_hash("abc"))
        )).collect::<Vec<_>>();
        let membership =
            crate::ProgramMembership::single("root", docs.iter().map(|d| d.uri.clone()));
        let mut resolver = |_: &SourceIdentity| Ok(std::sync::Arc::<str>::from("abc"));
        let p = crate::load_with_resolver(&membership, &docs, Some(&mut resolver)).unwrap();
        let targets = TargetIndex::new(&p);
        for doc in &docs {
            let tree = parser().parse(&*doc.text, None).unwrap();
            let mut suffixes = vec![];
            collect(tree.root_node(), &mut vec![], &mut suffixes);
            for (statement, _) in suffixes {
                assert_eq!(
                    targets.positions(&p, doc, statement),
                    scanned_positions(&p, doc, statement)
                );
            }
        }
        // Identical byte ranges in different files must retain their own sources.
        for (target, descriptors) in &p.embedded.associations {
            let OriginTarget::Occurrence(id) = target;
            let current = p.provenance.origins(*id)[0].span;
            let uri = &p.sources.snapshot(current.snapshot()).unwrap().uri;
            let expected = uri.replace("doc-", "source-").replace(".den", ".dsl");
            for d in descriptors {
                assert_eq!(d.source.uri, expected);
            }
            assert!(!p.embedded.provenance.origins(*id).is_empty());
        }
    }
}
