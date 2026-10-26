//! Recoverable editor projection and root-scoped incremental name resolution.
//! The caller owns parsing, buffers and membership; this layer performs no IO.
mod projection;
mod queries;
pub use denotate_analysis::{Role, RuleAnalysis, RuleSyntax, Symbol};
use denotate_ir::Namespace;
pub use projection::{Projection, Token};
pub use queries::Index;
use std::{collections::BTreeSet, ops::Range};

/// Exact name segments, excluding a leading global `::`. Quoted separators and
/// escapes use the loader's path tokenizer, not display-string splitting.
pub fn name_segments(raw: &str) -> Vec<Range<usize>> {
    let mut offset = 0;
    crate::ast::path_parts(raw)
        .into_iter()
        .filter_map(|part| {
            let span = offset..offset + part.len();
            offset += part.len() + 2;
            (!part.is_empty()).then_some(span)
        })
        .collect()
}

/// Parse one complete standalone reference using the loader's name rules.
pub fn parse_name(raw: &str) -> Result<Name, String> {
    let raw = raw.trim();
    let source = crate::SourceFile::new("argument", 0, raw);
    let name = crate::ast::reference_name(&source, 0..raw.len()).map_err(|e| {
        e.into_iter()
            .map(|d| d.message)
            .collect::<Vec<_>>()
            .join("; ")
    })?;
    Ok(Name {
        namespace: name.namespace,
        text: name.text,
        generated: name.generated,
    })
}

#[cfg(test)]
mod name_tests;

/// Decode a namespace path using the same rules as strict loading.
pub fn namespace_path(
    source: &crate::SourceFile,
    node: tree_sitter::Node<'_>,
) -> crate::Result<Namespace> {
    crate::ast::namespace_path(source, node)
}

/// The same visibility rule is used by strict loading and editor queries.
/// Enclosing scopes are candidates, not shadowing layers.
pub(crate) fn visible_namespaces<'a>(
    namespace: &Namespace,
    imports: impl IntoIterator<Item = &'a Namespace>,
    explicit: Option<&Namespace>,
) -> Vec<Namespace> {
    if let Some(namespace) = explicit {
        return vec![namespace.clone()];
    }
    let mut all: BTreeSet<_> = imports.into_iter().cloned().collect();
    for length in 0..=namespace.segments().len() {
        all.insert(Namespace::new(namespace.segments()[..length].iter().cloned()).unwrap());
    }
    all.into_iter().collect()
}
/// Canonical lookup keys, shared by strict arena construction and recoverable
/// resolution. Storage and duplicate handling differ; name identity does not.
pub(crate) fn candidate_keys(
    namespaces: Vec<Namespace>,
    text: &str,
    generated: bool,
) -> Vec<(Namespace, String, bool)> {
    namespaces
        .into_iter()
        .map(|namespace| (namespace, text.to_owned(), generated))
        .collect()
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Scope {
    pub namespace: Namespace,
    pub imports: Vec<Namespace>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Name {
    pub namespace: Option<Namespace>,
    pub text: String,
    pub generated: bool,
}
impl Name {
    pub fn bare(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            ..Self::default()
        }
    }
    pub fn spelling(&self) -> String {
        let name = if self.text.starts_with('$') && !self.generated {
            quoted(&self.text)
        } else {
            quote(&self.text)
        };
        self.namespace.as_ref().map_or(name.clone(), |ns| {
            let prefix = crate::ast::namespace_key(ns);
            if prefix.is_empty() {
                format!("::{name}")
            } else {
                format!("{prefix}::{name}")
            }
        })
    }
}
pub fn quote(text: &str) -> String {
    if !text.is_empty()
        && !crate::reserved_word(text)
        && (text.as_bytes()[0].is_ascii_alphabetic() || text.starts_with('$'))
        && text
            .trim_start_matches('$')
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        text.into()
    } else {
        quoted(text)
    }
}
pub fn quoted(text: &str) -> String {
    format!(
        "'{}'",
        text.replace('\\', "\\\\")
            .replace('\'', "\\'")
            .replace('\n', "\\n")
            .replace('\r', "\\r")
            .replace('\t', "\\t")
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    Namespace,
    Sort,
    Relation,
    Constant,
    Parameter,
    Contract,
    Alias,
}
impl Kind {
    pub fn label(self) -> &'static str {
        match self {
            Self::Namespace => "namespace",
            Self::Sort => "sort",
            Self::Relation => "relation",
            Self::Constant => "constant",
            Self::Parameter => "parameter",
            Self::Contract => "contract",
            Self::Alias => "location alias",
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub id: String,
    pub kind: Kind,
    pub contract: Option<ContractKind>,
    pub name: Name,
    pub scope: Scope,
    pub input: bool,
    pub parameters: Option<Vec<(String, Option<Name>)>>,
    pub sort: Option<Name>,
    pub parent: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ContractKind {
    Assumption,
    Obligation,
    Verification,
}
impl ContractKind {
    pub fn label(self) -> &'static str {
        match self {
            Self::Assumption => "assumption",
            Self::Obligation => "obligation",
            Self::Verification => "verification",
        }
    }
}

#[derive(Clone, Debug)]
pub struct VerificationReferences {
    pub scope: Scope,
    pub assumptions: Vec<(Name, Range<usize>)>,
    pub obligations: Vec<(Name, Range<usize>)>,
}

fn matching_contracts<'a, T>(
    scope: &Scope,
    name: &Name,
    entries: &'a [(Namespace, String, ContractKind, T)],
) -> Vec<&'a (Namespace, String, ContractKind, T)> {
    let candidates = candidate_keys(
        visible_namespaces(&scope.namespace, &scope.imports, name.namespace.as_ref()),
        &name.text,
        name.generated,
    );
    entries
        .iter()
        .filter(|(ns, text, _, _)| candidates.contains(&(ns.clone(), text.clone(), false)))
        .collect()
}

/// Shared contract reference resolution for strict loading and recoverable indexing.
pub(crate) fn resolve_contract_list<T: Clone + Ord>(
    scope: &Scope,
    names: impl IntoIterator<Item = (Name, Range<usize>)>,
    kind: ContractKind,
    entries: &[(Namespace, String, ContractKind, T)],
) -> Result<Vec<T>, Vec<(Range<usize>, String)>> {
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    let mut errors = Vec::new();
    for (name, span) in names {
        let matching = matching_contracts(scope, &name, entries);
        let expected = matching.iter().filter(|e| e.2 == kind).collect::<Vec<_>>();
        let message = match expected.as_slice() {
            [entry] => {
                if seen.insert(entry.3.clone()) {
                    selected.push(entry.3.clone());
                    None
                } else {
                    Some(format!(
                        "Duplicate {} reference {:?}",
                        kind.label(),
                        name.spelling()
                    ))
                }
            }
            [] if !matching.is_empty() => Some(format!(
                "Expected {} {:?}; name has a different contract kind",
                kind.label(),
                name.spelling()
            )),
            [] => Some(format!("Unknown {} {:?}", kind.label(), name.spelling())),
            _ => Some(format!(
                "Ambiguous {} {:?}; qualify it with its namespace",
                kind.label(),
                name.spelling()
            )),
        };
        if let Some(message) = message {
            errors.push((span, message));
        }
    }
    if errors.is_empty() {
        Ok(selected)
    } else {
        Err(errors)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expected {
    Argument(Name, usize),
    Sort(Name),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lookup {
    Name(Kind),
    Constant(Expected),
    Anonymous(Expected),
    Parameter(Name),
    Variable { rule: String, occurrence: String },
    Declaration(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pub name: Name,
    pub scope: Scope,
    pub span: Range<usize>,
    pub lookup: Lookup,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub syntax: RuleSyntax,
    pub scope: Scope,
    pub relations: Vec<Name>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Issue {
    pub span: Range<usize>,
    pub code: String,
    pub message: String,
    pub warning: bool,
}
