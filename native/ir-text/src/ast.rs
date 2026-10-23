use crate::{Result, SourceFile, error, parser};
use std::{collections::BTreeMap, ops::Range};
use tree_sitter::Node;

#[derive(Clone, Debug)]
pub(crate) struct Name {
    pub module: Option<String>,
    pub text: String,
    pub generated: bool,
    pub span: Range<usize>,
}
impl Name {
    pub fn identity(&self) -> (Option<&str>, &str, bool) {
        (self.module.as_deref(), &self.text, self.generated)
    }
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
    Domain(Name, Vec<Name>),
}
#[derive(Clone, Debug)]
pub(crate) struct Statement {
    pub decl: Decl,
    pub span: Range<usize>,
    pub semantic: String,
}
#[derive(Clone, Debug)]
pub(crate) struct Module {
    pub source: SourceFile,
    pub name: String,
    pub ownership: String,
    pub imports: Vec<Name>,
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
fn name(source: &SourceFile, node: Node<'_>) -> Result<Name> {
    name_in(source, node, false)
}
fn name_in(source: &SourceFile, node: Node<'_>, parameter: bool) -> Result<Name> {
    if node.kind() == "qualified_name" {
        let raw = text(source, node);
        let mut in_quote = false;
        let mut escaped = false;
        let mut split = None;
        for (i, c) in raw.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            if in_quote && c == '\\' {
                escaped = true;
                continue;
            }
            if c == '\'' {
                in_quote = !in_quote;
            }
            if !in_quote && raw[i..].starts_with("::") {
                split = Some(i);
                break;
            }
        }
        let i =
            split.ok_or_else(|| error(source, node.byte_range(), "Invalid qualified reference"))?;
        let decode = |s: &str| -> Result<String> {
            if s.starts_with('\'') {
                quoted_text(source, s, node.byte_range())
            } else if crate::reserved_word(s) {
                Err(error(
                    source,
                    node.byte_range(),
                    "Reserved word must be quoted",
                ))
            } else if s.starts_with('-') || s.as_bytes()[0].is_ascii_digit() {
                Ok(s.parse::<i64>()
                    .map_err(|_| {
                        error(
                            source,
                            node.byte_range(),
                            "Expected a signed 64-bit integer",
                        )
                    })?
                    .to_string())
            } else {
                Ok(s.to_owned())
            }
        };
        let member = &raw[i + 2..];
        return Ok(Name {
            module: Some(decode(&raw[..i])?),
            text: decode(member)?,
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
        module: None,
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
fn syntax_errors(source: &SourceFile, node: Node<'_>, out: &mut Vec<crate::Diagnostic>) {
    if node.is_error() || node.is_missing() {
        // Recovery can turn a declaration with a reserved name into one ERROR
        // node. Keep the useful name diagnostic instead of hiding it behind
        // a generic syntax error. Use parser leaves, so comments and quoted
        // strings cannot masquerade as declaration keywords.
        fn leaves<'a>(node: Node<'a>, out: &mut Vec<Node<'a>>) {
            if node.kind() == "comment" {
                return;
            }
            if node.child_count() == 0 {
                out.push(node);
            } else {
                for child in node.children(&mut node.walk()) {
                    leaves(child, out);
                }
            }
        }
        let mut tokens = Vec::new();
        leaves(node, &mut tokens);
        if let Some(pair) = tokens.windows(2).find(|pair| {
            matches!(
                text(source, pair[0]),
                "relation" | "input" | "sort" | "const" | "module" | "use"
            ) && crate::reserved_word(text(source, pair[1]))
        }) {
            out.extend(error(
                source,
                pair[1].byte_range(),
                "Reserved word must be quoted",
            ));
            return;
        }
        out.extend(error(
            source,
            node.byte_range(),
            if node.is_missing() {
                format!("Expected {}", node.kind())
            } else {
                "Invalid .den syntax".into()
            },
        ));
        return;
    }
    for child in node.children(&mut node.walk()) {
        syntax_errors(source, child, out);
    }
}
fn semantic_atom(a: &Atom) -> String {
    format!(
        "{:?}:{:?}",
        a.name.identity(),
        a.terms
            .iter()
            .map(|t| (t.name.identity(), t.variable, t.anonymous))
            .collect::<Vec<_>>()
    )
}
fn semantic(d: &Decl) -> String {
    match d {
        Decl::Rule(h, b) => format!(
            "rule:{}:{:?}",
            semantic_atom(h),
            b.iter()
                .map(|(neg, a)| (*neg, semantic_atom(a)))
                .collect::<Vec<_>>()
        ),
        Decl::Sort(n) => format!("sort:{:?}", n.identity()),
        Decl::Constants(ns, s) => format!(
            "constants:{:?}:{:?}",
            ns.iter().map(Name::identity).collect::<Vec<_>>(),
            s.identity()
        ),
        Decl::Relation(n, input, ps) => format!(
            "relation:{:?}:{input}:{:?}",
            n.identity(),
            ps.iter()
                .map(|(n, s)| (n.identity(), s.identity()))
                .collect::<Vec<_>>()
        ),
        Decl::Contract {
            name,
            assumption,
            relation,
            columns,
            message,
        } => format!(
            "contract:{:?}:{assumption}:{:?}:{:?}:{message:?}",
            name.identity(),
            relation.identity(),
            columns.iter().map(Name::identity).collect::<Vec<_>>()
        ),
        Decl::Domain(s, ns) => format!(
            "domain:{:?}:{:?}",
            s.identity(),
            ns.iter().map(Name::identity).collect::<Vec<_>>()
        ),
    }
}
/// Extract the header even from an incomplete document, so unrelated broken
/// files do not prevent loading a valid root and missing imports remain precise.
pub(crate) fn header(source: &SourceFile) -> Option<String> {
    let tree = parser().parse(source.text.as_ref(), None)?;
    let m = children(tree.root_node())
        .into_iter()
        .find(|n| n.kind() == "module")?;
    name(source, m.child_by_field_name("name")?)
        .ok()
        .map(|n| n.text)
}
pub(crate) fn parse(source: &SourceFile) -> Result<Module> {
    let tree = parser()
        .parse(source.text.as_ref(), None)
        .ok_or_else(|| error(source, 0..0, "Parser stopped"))?;
    let root = tree.root_node();
    let mut errors = Vec::new();
    syntax_errors(source, root, &mut errors);
    if !errors.is_empty() {
        return Err(errors);
    }
    let module = children(root)
        .into_iter()
        .find(|n| n.kind() == "module")
        .ok_or_else(|| error(source, 0..0, "Missing module"))?;
    let module_name = name(source, field(source, module, "name")?)?.text;
    let ownership = module
        .child_by_field_name("ownership")
        .map(|n| text(source, n))
        .unwrap_or("user")
        .to_owned();
    let mut out = Module {
        source: source.clone(),
        name: module_name,
        ownership,
        imports: Vec::new(),
        statements: Vec::new(),
        locations: Vec::new(),
    };
    let mut aliases = BTreeMap::new();
    for node in children(root) {
        let decl = match node.kind() {
            "module" | "comment" => continue,
            "import" => {
                out.imports
                    .push(name(source, field(source, node, "name")?)?);
                continue;
            }
            "source_location" | "location_alias" => {
                let alias = text(source, field(source, node, "name")?).to_owned();
                if aliases.insert(alias, node.byte_range()).is_some() {
                    return Err(error(source, node.byte_range(), "Duplicate location alias"));
                }
                out.locations.push(node.byte_range());
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
            out.locations.push(loc.byte_range());
        }
        let signature = semantic(&decl);
        out.statements.push(Statement {
            decl,
            span: node.byte_range(),
            semantic: signature,
        });
    }
    Ok(out)
}
