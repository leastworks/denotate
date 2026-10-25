use crate::{Result, SourceFile, error, parser};
use denotate_ir::Namespace;
use std::{collections::BTreeMap, ops::Range};
use tree_sitter::Node;

#[derive(Clone, Debug)]
pub(crate) struct Name {
    pub namespace: Option<Namespace>,
    pub text: String,
    pub generated: bool,
    pub span: Range<usize>,
}
#[derive(Clone, Debug)]
pub(crate) struct Term {
    pub name: Name,
    pub variable: bool,
    pub anonymous: bool,
}
#[derive(Clone, Debug)]
pub(crate) struct Atom {
    pub name: Name,
    pub terms: Vec<Term>,
    pub span: Range<usize>,
}
#[derive(Clone, Debug)]
pub(crate) enum Decl {
    Sort(Name),
    Constants(Vec<Name>, Name),
    Relation(Name, bool, Vec<(Name, Name)>),
    Rule(Atom, Vec<(bool, Atom)>),
    Contract {
        name: Name,
        assumption: bool,
        relation: Name,
        columns: Vec<Name>,
        message: String,
    },
    Verification {
        name: Name,
        assumptions: Vec<Name>,
        obligations: Vec<Name>,
    },
    Domain(Name, Vec<Name>),
}
#[derive(Clone, Debug)]
pub(crate) struct Statement {
    pub decl: Decl,
    pub span: Range<usize>,
}
#[derive(Clone, Debug)]
pub(crate) struct Scope {
    pub source: SourceFile,
    pub namespace: Namespace,
    pub imports: Vec<(Namespace, Range<usize>)>,
    pub statements: Vec<Statement>,
    /// Step 2 interprets these annotations; step 1 retains their exact syntax
    /// independently of semantic identities and current .den provenance.
    pub locations: Vec<Range<usize>>,
}

fn field<'a>(source: &SourceFile, node: Node<'a>, key: &str) -> Result<Node<'a>> {
    node.child_by_field_name(key)
        .ok_or_else(|| error(source, node.byte_range(), format!("Missing {key}")))
}
fn children(node: Node<'_>) -> Vec<Node<'_>> {
    node.named_children(&mut node.walk()).collect()
}
fn text<'a>(source: &'a SourceFile, node: Node<'_>) -> &'a str {
    &source.text[node.byte_range()]
}

fn quoted_text(source: &SourceFile, raw: &str, span: Range<usize>) -> Result<String> {
    if raw.len() < 2 || !raw.starts_with('\'') || !raw.ends_with('\'') {
        return Err(error(source, span, "Incomplete quoted name"));
    }
    let mut out = String::new();
    let mut chars = raw[1..raw.len() - 1].chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        out.push(match chars.next() {
            Some('\\') => '\\',
            Some('\'') => '\'',
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            _ => {
                return Err(error(
                    source,
                    span.clone(),
                    "Unsupported quoted-name escape; use \\\\, \\', \\n, \\r or \\t",
                ));
            }
        });
    }
    if out.is_empty() {
        return Err(error(source, span.clone(), "Names must not be empty"));
    }
    Ok(out)
}
pub(crate) fn name(source: &SourceFile, node: Node<'_>) -> Result<Name> {
    name_in(source, node, false)
}
pub(crate) fn name_in(source: &SourceFile, node: Node<'_>, parameter: bool) -> Result<Name> {
    if node.kind() == "qualified_name" {
        let mut parts = path_parts(text(source, node));
        if parts.first() == Some(&"") {
            parts.remove(0);
        }
        let member = parts.pop().unwrap();
        let module = namespace_parts(source, &parts, node.byte_range())?;
        return Ok(Name {
            namespace: Some(module),
            text: decode(source, member, node.byte_range())?,
            generated: member.starts_with('$'),
            span: node.byte_range(),
        });
    }
    let spelling = match node.kind() {
        "quoted_identifier" => quoted_text(source, text(source, node), node.byte_range())?,
        "integer" => text(source, node)
            .parse::<i64>()
            .map_err(|_| {
                error(
                    source,
                    node.byte_range(),
                    "Expected a signed 64-bit integer",
                )
            })?
            .to_string(),
        "variable" if text(source, node).starts_with('?') => {
            let quoted = children(node)
                .into_iter()
                .find(|n| n.kind() == "quoted_identifier")
                .ok_or_else(|| error(source, node.byte_range(), "Missing variable name"))?;
            quoted_text(source, text(source, quoted), node.byte_range())?
        }
        _ => text(source, node).to_owned(),
    };
    if !parameter
        && matches!(node.kind(), "constant" | "identifier")
        && crate::reserved_word(&spelling)
    {
        return Err(error(
            source,
            node.byte_range(),
            "Reserved word must be quoted",
        ));
    }
    Ok(Name {
        namespace: None,
        text: spelling,
        generated: node.kind() == "generated_identifier",
        span: node.byte_range(),
    })
}
fn atom(source: &SourceFile, node: Node<'_>) -> Result<Atom> {
    let relation = field(source, node, "name")?;
    let mut terms = Vec::new();
    for n in children(node)
        .into_iter()
        .filter(|n| n.id() != relation.id() && n.kind() != "comment")
    {
        terms.push(Term {
            name: name(source, n)?,
            variable: n.kind() == "variable",
            anonymous: n.kind() == "anonymous",
        });
    }
    Ok(Atom {
        name: name(source, relation)?,
        terms,
        span: node.byte_range(),
    })
}
pub(crate) fn syntax_errors(source: &SourceFile, root: Node<'_>, out: &mut Vec<crate::Diagnostic>) {
    // Recovery may keep the declaration keyword outside the ERROR node holding
    // its invalid name. Inspect the whole token stream, not individual error
    // subtrees. Comments and quoted names are leaves, never scanned as code.
    fn leaves<'a>(node: Node<'a>, out: &mut Vec<Node<'a>>) {
        if node.kind() == "comment" {
            return;
        }
        if node.child_count() == 0 {
            if !node.is_missing() {
                out.push(node);
            }
        } else {
            for child in node.children(&mut node.walk()) {
                leaves(child, out);
            }
        }
    }
    let mut tokens = Vec::new();
    leaves(root, &mut tokens);
    let reserved_names: Vec<_> = tokens
        .windows(2)
        .filter_map(|pair| {
            (matches!(
                text(source, pair[0]),
                "relation" | "input" | "sort" | "const" | "module" | "namespace" | "use"
            ) && crate::reserved_word(text(source, pair[1])))
            .then(|| pair[1].byte_range())
        })
        .collect();

    fn visit(
        source: &SourceFile,
        node: Node<'_>,
        reserved_names: &[Range<usize>],
        out: &mut Vec<crate::Diagnostic>,
    ) {
        if node.is_error() || node.is_missing() {
            let names: Vec<_> = reserved_names
                .iter()
                .filter(|range| node.start_byte() <= range.start && range.end <= node.end_byte())
                .collect();
            if !names.is_empty() {
                for range in names {
                    out.extend(error(source, range.clone(), "Reserved word must be quoted"));
                }
            } else {
                out.extend(error(
                    source,
                    node.byte_range(),
                    if node.is_missing() {
                        format!("Expected {}", node.kind())
                    } else {
                        "Invalid .den syntax".into()
                    },
                ));
            }
            return;
        }
        for child in node.children(&mut node.walk()) {
            visit(source, child, reserved_names, out);
        }
    }
    visit(source, root, &reserved_names, out);
}

// Delimit only outside quoted segments, retaining escaped quotes verbatim.
pub(crate) fn path_parts(raw: &str) -> Vec<&str> {
    let (mut quoted, mut escaped, mut start) = (false, false, 0);
    let mut parts = Vec::new();
    for (i, c) in raw.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if quoted && c == '\\' {
            escaped = true;
            continue;
        }
        if c == '\'' {
            quoted = !quoted;
        }
        if !quoted && raw[i..].starts_with("::") {
            parts.push(&raw[start..i]);
            start = i + 2;
        }
    }
    parts.push(&raw[start..]);
    parts
}
fn decode(source: &SourceFile, raw: &str, span: Range<usize>) -> Result<String> {
    if raw.starts_with('\'') {
        return quoted_text(source, raw, span);
    }
    if crate::reserved_word(raw) {
        return Err(error(source, span, "Reserved word must be quoted"));
    }
    if raw.starts_with('-') || raw.as_bytes()[0].is_ascii_digit() {
        return raw
            .parse::<i64>()
            .map(|n| n.to_string())
            .map_err(|_| error(source, span, "Expected a signed 64-bit integer"));
    }
    Ok(raw.to_owned())
}
fn namespace_parts(source: &SourceFile, parts: &[&str], span: Range<usize>) -> Result<Namespace> {
    let mut decoded = Vec::new();
    for raw in parts {
        if raw.is_empty() || (!raw.starts_with('\'') && !raw.as_bytes()[0].is_ascii_alphabetic()) {
            return Err(error(
                source,
                span,
                "Namespace segments must be identifiers or quoted names",
            ));
        }
        decoded.push(decode(source, raw, span.clone())?);
    }
    Ok(Namespace::new(decoded).expect("decoded names are nonempty"))
}
pub(crate) fn namespace_path(source: &SourceFile, node: Node<'_>) -> Result<Namespace> {
    namespace_parts(source, &path_parts(text(source, node)), node.byte_range())
}
/// A collision-free, readable encoding for the existing semantic-key namespace field.
/// Quoted `a::b` remains distinct from the two segments `a` and `b`.
pub(crate) fn namespace_key(namespace: &Namespace) -> String {
    namespace
        .segments()
        .iter()
        .map(|s| {
            if s.as_bytes()[0].is_ascii_alphabetic()
                && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                && !crate::reserved_word(s)
            {
                s.clone()
            } else {
                format!(
                    "'{}'",
                    s.replace('\\', "\\\\")
                        .replace('\'', "\\'")
                        .replace('\n', "\\n")
                        .replace('\r', "\\r")
                        .replace('\t', "\\t")
                )
            }
        })
        .collect::<Vec<_>>()
        .join("::")
}
pub(crate) fn parse(source: &SourceFile) -> Result<Vec<Scope>> {
    let tree = parser()
        .parse(source.text.as_ref(), None)
        .ok_or_else(|| error(source, 0..0, "Parser stopped"))?;
    let root = tree.root_node();
    let mut errors = Vec::new();
    syntax_errors(source, root, &mut errors);
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut out = Vec::new();
    let mut aliases = BTreeMap::new();
    scope(
        source,
        root,
        Namespace::default(),
        &[],
        true,
        &mut aliases,
        &mut out,
    )?;
    Ok(out)
}

// Each statement retains its lexical scope; this also preserves source order
// when a file interleaves global declarations and nested namespace blocks.
fn scope(
    source: &SourceFile,
    root: Node<'_>,
    mut namespace: Namespace,
    inherited: &[(Namespace, Range<usize>)],
    top: bool,
    aliases: &mut BTreeMap<String, Range<usize>>,
    out: &mut Vec<Scope>,
) -> Result<()> {
    let nodes = children(root)
        .into_iter()
        .filter(|n| {
            root.child_by_field_name("name")
                .is_none_or(|name| n.id() != name.id())
        })
        .collect::<Vec<_>>();
    let is_block = |n: &Node<'_>| {
        n.kind() == "namespace" && n.children(&mut n.walk()).any(|child| child.kind() == "{")
    };
    let headers = nodes
        .iter()
        .filter(|n| n.kind() == "module" || (n.kind() == "namespace" && !is_block(n)))
        .collect::<Vec<_>>();
    if !headers.is_empty() && (!top || headers.len() > 1 || nodes.iter().any(is_block)) {
        return Err(error(
            source,
            headers[0].byte_range(),
            "A file-scoped namespace cannot be nested, repeated or mixed with top-level namespace blocks",
        ));
    }
    let mut imports = inherited.to_vec();
    for node in nodes.iter().filter(|n| n.kind() == "import") {
        let n = field(source, *node, "name")?;
        imports.push((namespace_path(source, n)?, n.byte_range()));
    }
    out.push(Scope {
        source: source.clone(),
        namespace: namespace.clone(),
        imports: imports.clone(),
        statements: Vec::new(),
        locations: Vec::new(),
    });
    for node in nodes {
        let mut item = Scope {
            source: source.clone(),
            namespace: namespace.clone(),
            imports: imports.clone(),
            statements: Vec::new(),
            locations: Vec::new(),
        };
        let decl = match node.kind() {
            "comment" | "import" => continue,
            "module" | "namespace" => {
                let path = namespace_path(source, field(source, node, "name")?)?;
                if is_block(&node) {
                    let nested =
                        Namespace::new(namespace.segments().iter().chain(path.segments()).cloned())
                            .unwrap();
                    scope(source, node, nested, &imports, false, aliases, out)?;
                } else {
                    namespace = path;
                    item.namespace = namespace.clone();
                    out.push(item);
                }
                continue;
            }
            "source_location" | "location_alias" => {
                let alias = text(source, field(source, node, "name")?).to_owned();
                if aliases.insert(alias, node.byte_range()).is_some() {
                    return Err(error(source, node.byte_range(), "Duplicate location alias"));
                }
                item.locations.push(node.byte_range());
                out.push(item);
                continue;
            }
            "sort" => Decl::Sort(name(source, field(source, node, "name")?)?),
            "constants" => Decl::Constants(
                node.children_by_field_name("name", &mut node.walk())
                    .map(|n| name(source, n))
                    .collect::<Result<_>>()?,
                name(source, field(source, node, "sort")?)?,
            ),
            "relation" => {
                let params = children(node)
                    .into_iter()
                    .filter(|n| n.kind() == "parameter")
                    .map(|p| {
                        Ok((
                            name_in(source, field(source, p, "name")?, true)?,
                            name(source, field(source, p, "sort")?)?,
                        ))
                    })
                    .collect::<Result<_>>()?;
                Decl::Relation(
                    name(source, field(source, node, "name")?)?,
                    text(source, field(source, node, "kind")?) == "input",
                    params,
                )
            }
            "statement" => {
                let head = field(source, node, "head")?;
                let mut body = Vec::new();
                for n in children(node).into_iter().filter(|n| n.id() != head.id()) {
                    if n.kind() == "positive_atom" {
                        body.push((false, atom(source, n)?));
                    }
                    if n.kind() == "negative_atom" {
                        let a = children(n)
                            .into_iter()
                            .find(|n| n.kind() == "atom")
                            .ok_or_else(|| {
                                error(source, n.byte_range(), "Missing negative atom")
                            })?;
                        let mut atom = atom(source, a)?;
                        atom.span = n.byte_range();
                        body.push((true, atom));
                    }
                }
                Decl::Rule(atom(source, head)?, body)
            }
            "obligation" | "assumption" => {
                let card = children(node)
                    .into_iter()
                    .find(|n| n.kind() == "cardinality")
                    .ok_or_else(|| error(source, node.byte_range(), "Missing cardinality"))?;
                Decl::Contract {
                    name: name(source, field(source, node, "name")?)?,
                    assumption: node.kind() == "assumption",
                    relation: name(source, field(source, card, "relation")?)?,
                    columns: card
                        .children_by_field_name("column", &mut card.walk())
                        .map(|n| name_in(source, n, true))
                        .collect::<Result<_>>()?,
                    message: node
                        .child_by_field_name("message")
                        .map(|n| {
                            serde_json::from_str(text(source, n))
                                .map_err(|e| error(source, n.byte_range(), e.to_string()))
                        })
                        .transpose()?
                        .unwrap_or_default(),
                }
            }
            "verification" => Decl::Verification {
                name: name(source, field(source, node, "name")?)?,
                assumptions: node
                    .children_by_field_name("assumption", &mut node.walk())
                    .map(|n| name(source, n))
                    .collect::<Result<_>>()?,
                obligations: node
                    .children_by_field_name("obligation", &mut node.walk())
                    .map(|n| name(source, n))
                    .collect::<Result<_>>()?,
            },
            "domain" => Decl::Domain(
                name(source, field(source, node, "sort")?)?,
                node.children_by_field_name("value", &mut node.walk())
                    .map(|n| name(source, n))
                    .collect::<Result<_>>()?,
            ),
            _ => {
                return Err(error(
                    source,
                    node.byte_range(),
                    format!("Unsupported declaration {}", node.kind()),
                ));
            }
        };
        for loc in children(node)
            .into_iter()
            .filter(|n| n.kind() == "location")
        {
            item.locations.push(loc.byte_range());
        }
        item.statements.push(Statement {
            decl,
            span: node.byte_range(),
        });
        out.push(item);
    }
    Ok(())
}
