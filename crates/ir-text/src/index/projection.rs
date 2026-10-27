use super::*;
use crate::{SourceFile, ast};
use denotate_analysis::{NamedDeclaration, RuleAtom};
use std::collections::{BTreeMap, HashMap};
use tree_sitter::{Node, Tree};

#[derive(Clone, Debug)]
pub struct Token {
    pub text: String,
    pub span: Range<usize>,
    pub comment: bool,
}
#[derive(Clone, Debug)]
pub struct Projection {
    pub source: SourceFile,
    pub tree: Tree,
    pub declarations: BTreeMap<String, Declaration>,
    pub anchors: BTreeMap<String, Range<usize>>,
    pub references: Vec<Reference>,
    pub verifications: Vec<VerificationReferences>,
    pub rules: BTreeMap<String, Rule>,
    pub rule_anchors: BTreeMap<String, BTreeMap<String, Range<usize>>>,
    pub scopes: Vec<(Range<usize>, Scope)>,
    pub tokens: Vec<Token>,
    pub issues: Vec<Issue>,
    nodes: HashMap<usize, String>,
    next_id: u64,
}
fn field<'a>(node: Node<'a>, key: &str) -> Option<Node<'a>> {
    node.child_by_field_name(key)
        .filter(|n| !n.is_missing() && !n.is_error())
}
fn decoded(source: &SourceFile, node: Node<'_>, parameter: bool) -> Option<Name> {
    if node.is_missing() || node.is_error() {
        return None;
    }
    let n = ast::name_in(source, node, parameter).ok()?;
    Some(Name {
        namespace: n.namespace,
        text: n.text,
        generated: n.generated,
    })
}
fn leaves(source: &SourceFile, node: Node<'_>, out: &mut Vec<Token>) {
    if node.is_missing() {
        return;
    }
    if node.child_count() == 0 || node.kind() == "variable" {
        if !node.byte_range().is_empty() {
            out.push(Token {
                text: source.text[node.byte_range()].into(),
                span: node.byte_range(),
                comment: node.kind() == "comment",
            });
        }
    } else {
        for child in node.children(&mut node.walk()) {
            leaves(source, child, out);
        }
    }
}
impl Projection {
    /// Consume the caller's current incremental tree. No parsing is performed.
    pub fn new(source: SourceFile, tree: Tree, previous: Option<&Self>) -> Self {
        let mut out = Self {
            source,
            tree: tree.clone(),
            declarations: BTreeMap::new(),
            anchors: BTreeMap::new(),
            references: vec![],
            verifications: vec![],
            rules: BTreeMap::new(),
            rule_anchors: BTreeMap::new(),
            scopes: vec![],
            tokens: vec![],
            issues: vec![],
            nodes: HashMap::new(),
            next_id: previous.map_or(0, |p| p.next_id),
        };
        leaves(&out.source, tree.root_node(), &mut out.tokens);
        out.block(tree.root_node(), Scope::default(), previous);
        fn verification_syntax(source: &SourceFile, node: Node<'_>, out: &mut Vec<Issue>) {
            fn keyword(node: Node<'_>) -> bool {
                (node.kind() == "verification" && !node.is_named())
                    || node.children(&mut node.walk()).any(keyword)
            }
            if !node.has_error() {
                return;
            }
            if (node.kind() == "verification" && node.is_named())
                || (node.is_error() && keyword(node))
            {
                let mut errors = Vec::new();
                ast::syntax_errors(source, node, &mut errors);
                out.extend(errors.into_iter().map(|d| Issue {
                    span: d.range,
                    code: "verification-syntax".into(),
                    message: d.message,
                    warning: false,
                }));
            } else {
                for child in node.children(&mut node.walk()) {
                    verification_syntax(source, child, out);
                }
            }
        }
        verification_syntax(&out.source, tree.root_node(), &mut out.issues);
        if let Some(previous) = previous {
            out.reconcile_renamed_declarations(previous);
        }
        out
    }
    fn reconcile_renamed_declarations(&mut self, previous: &Self) {
        // IDs are opaque and independent of spelling. After matching unchanged
        // declarations, a unique replacement in the same kind/lexical namespace
        // retains identity (e.g. typing a new declaration name). Ambiguous edits
        // allocate fresh identities instead of guessing correspondence.
        let mut remap = BTreeMap::new();
        for d in self
            .declarations
            .values()
            .filter(|d| !previous.declarations.contains_key(&d.id))
        {
            let same_group = |other: &&Declaration| {
                other.kind == d.kind
                    && other.contract == d.contract
                    && other.scope.namespace == d.scope.namespace
                    && other.parent == d.parent
            };
            let old = previous
                .declarations
                .values()
                .filter(|old| !self.declarations.contains_key(&old.id))
                .filter(same_group)
                .collect::<Vec<_>>();
            let new_count = self
                .declarations
                .values()
                .filter(|n| !previous.declarations.contains_key(&n.id))
                .filter(same_group)
                .count();
            if let ([old], 1) = (old.as_slice(), new_count) {
                remap.insert(d.id.clone(), old.id.clone());
            }
        }
        for d in self
            .declarations
            .values()
            .filter(|d| d.kind == Kind::Parameter && !previous.declarations.contains_key(&d.id))
        {
            let parent = d.parent.as_ref().map(|id| remap.get(id).unwrap_or(id));
            if let Some(old) = previous.declarations.values().find(|old| {
                old.kind == d.kind
                    && old.name == d.name
                    && old.scope.namespace == d.scope.namespace
                    && old.parent.as_ref() == parent
                    && !self.declarations.contains_key(&old.id)
                    && !remap.values().any(|id| id == &old.id)
            }) {
                remap.insert(d.id.clone(), old.id.clone());
            }
        }
        if remap.is_empty() {
            return;
        }
        self.declarations = std::mem::take(&mut self.declarations)
            .into_values()
            .map(|mut d| {
                if let Some(id) = remap.get(&d.id) {
                    d.id = id.clone();
                }
                if let Some(parent) = d.parent.as_mut() {
                    if let Some(id) = remap.get(parent) {
                        *parent = id.clone();
                    }
                }
                (d.id.clone(), d)
            })
            .collect();
        self.anchors = std::mem::take(&mut self.anchors)
            .into_iter()
            .map(|(id, span)| (remap.get(&id).cloned().unwrap_or(id), span))
            .collect();
        for id in self.nodes.values_mut() {
            if let Some(new) = remap.get(id) {
                *id = new.clone();
            }
        }
        for r in &mut self.references {
            if let Lookup::Declaration(id) = &mut r.lookup {
                if let Some(new) = remap.get(id) {
                    *id = new.clone();
                }
            }
        }
    }
    fn name(&mut self, node: Node<'_>, parameter: bool) -> Option<Name> {
        if node.is_missing() || node.is_error() {
            return None;
        }
        match ast::name_in(&self.source, node, parameter) {
            Ok(n) => Some(Name {
                namespace: n.namespace,
                text: n.text,
                generated: n.generated,
            }),
            Err(errors) => {
                for e in errors {
                    let issue = Issue {
                        span: e.range,
                        code: "name-syntax".into(),
                        message: e.message,
                        warning: false,
                    };
                    if !self.issues.contains(&issue) {
                        self.issues.push(issue);
                    }
                }
                None
            }
        }
    }
    fn reference(&mut self, node: Node<'_>, scope: &Scope, lookup: Lookup) -> Option<Name> {
        let name = self.name(node, matches!(lookup, Lookup::Parameter(_)))?;
        self.references.push(Reference {
            name: name.clone(),
            scope: scope.clone(),
            span: node.byte_range(),
            lookup,
        });
        Some(name)
    }
    fn declare(
        &mut self,
        node: Node<'_>,
        scope: &Scope,
        kind: Kind,
        parent: Option<String>,
        previous: Option<&Self>,
    ) -> Option<String> {
        let name = self.name(node, kind == Kind::Parameter)?;
        let contract = match node.parent().map(|p| p.kind()) {
            Some("assumption") => Some(ContractKind::Assumption),
            Some("obligation") => Some(ContractKind::Obligation),
            Some("verification") => Some(ContractKind::Verification),
            _ => None,
        };
        // Reused tree nodes retain identity even when their anchor moves. When
        // Tree-sitter rebuilt a parent, match the same semantic declaration.
        let old = previous.and_then(|p| {
            p.nodes.get(&node.id()).cloned().or_else(|| {
                p.declarations
                    .values()
                    .find(|d| {
                        d.kind == kind
                            && d.contract == contract
                            && (d.name == name || kind == Kind::Namespace)
                            && d.scope.namespace == scope.namespace
                            && d.parent == parent
                            && !self.declarations.contains_key(&d.id)
                    })
                    .map(|d| d.id.clone())
            })
        });
        let id = old
            .filter(|id| !self.declarations.contains_key(id))
            .unwrap_or_else(|| {
                let id = format!("d{}", self.next_id);
                self.next_id += 1;
                id
            });
        self.nodes.insert(node.id(), id.clone());
        self.anchors.insert(id.clone(), node.byte_range());
        self.references.push(Reference {
            name: name.clone(),
            scope: scope.clone(),
            span: node.byte_range(),
            lookup: Lookup::Declaration(id.clone()),
        });
        self.declarations.insert(
            id.clone(),
            Declaration {
                id: id.clone(),
                kind,
                contract,
                name,
                scope: scope.clone(),
                input: false,
                parameters: None,
                sort: None,
                parent,
            },
        );
        Some(id)
    }
    fn block(&mut self, root: Node<'_>, mut scope: Scope, previous: Option<&Self>) {
        let nodes: Vec<_> = root
            .named_children(&mut root.walk())
            .filter(|n| field(root, "name").is_none_or(|name| name.id() != n.id()))
            .collect();
        // Imports apply to the whole lexical block, including earlier declarations.
        for node in &nodes {
            if node.kind() == "import" {
                if let Some(path) =
                    field(*node, "name").and_then(|n| ast::namespace_path(&self.source, n).ok())
                {
                    scope.imports.push(path);
                }
            }
        }
        scope.imports.sort();
        scope.imports.dedup();
        let header = nodes.iter().find(|n| {
            matches!(n.kind(), "module" | "namespace")
                && !n.children(&mut n.walk()).any(|c| c.kind() == "{")
        });
        if let Some(path) = header
            .and_then(|n| field(*n, "name"))
            .and_then(|n| ast::namespace_path(&self.source, n).ok())
        {
            scope.namespace = path;
        }
        self.scopes.push((root.byte_range(), scope.clone()));
        for node in nodes {
            match node.kind() {
                "ERROR" => self.block(node, scope.clone(), previous),
                "module" | "namespace" => {
                    let Some(name_node) = field(node, "name") else {
                        continue;
                    };
                    let Ok(path) = ast::namespace_path(&self.source, name_node) else {
                        continue;
                    };
                    let block = node.children(&mut node.walk()).any(|c| c.kind() == "{");
                    let namespace = if block {
                        Namespace::new(
                            scope
                                .namespace
                                .segments()
                                .iter()
                                .chain(path.segments())
                                .cloned(),
                        )
                        .unwrap()
                    } else {
                        path
                    };
                    if let Some(id) = self.declare(
                        name_node,
                        &Scope {
                            namespace: namespace.clone(),
                            imports: scope.imports.clone(),
                        },
                        Kind::Namespace,
                        None,
                        previous,
                    ) {
                        let d = self.declarations.get_mut(&id).unwrap();
                        d.name = Name::bare(ast::namespace_key(&namespace));
                        d.scope.namespace = namespace.clone();
                    }
                    if block {
                        self.block(
                            node,
                            Scope {
                                namespace,
                                imports: scope.imports.clone(),
                            },
                            previous,
                        );
                    }
                }
                "import" => {
                    if let Some(n) = field(node, "name") {
                        if let Ok(path) = ast::namespace_path(&self.source, n) {
                            self.references.push(Reference {
                                name: Name::bare(ast::namespace_key(&path)),
                                scope: scope.clone(),
                                span: n.byte_range(),
                                lookup: Lookup::Name(Kind::Namespace),
                            });
                        }
                    }
                }
                "sort" => {
                    if let Some(n) = field(node, "name") {
                        self.declare(n, &scope, Kind::Sort, None, previous);
                    }
                }
                "constants" => {
                    let sort = field(node, "sort")
                        .and_then(|n| self.reference(n, &scope, Lookup::Name(Kind::Sort)));
                    for n in node.children_by_field_name("name", &mut node.walk()) {
                        if let Some(id) = self.declare(n, &scope, Kind::Constant, None, previous) {
                            self.declarations.get_mut(&id).unwrap().sort = sort.clone();
                        }
                    }
                }
                "relation" => {
                    let Some(n) = field(node, "name") else {
                        continue;
                    };
                    let Some(id) = self.declare(n, &scope, Kind::Relation, None, previous) else {
                        continue;
                    };
                    let mut parameters = vec![];
                    for param in node
                        .named_children(&mut node.walk())
                        .filter(|n| n.kind() == "parameter")
                    {
                        let sort = field(param, "sort")
                            .and_then(|n| self.reference(n, &scope, Lookup::Name(Kind::Sort)));
                        let name = field(param, "name")
                            .and_then(|n| {
                                let key = self.declare(
                                    n,
                                    &scope,
                                    Kind::Parameter,
                                    Some(id.clone()),
                                    previous,
                                )?;
                                self.declarations.get_mut(&key).unwrap().sort = sort.clone();
                                Some(self.declarations[&key].name.text.clone())
                            })
                            .unwrap_or_else(|| "?".into());
                        parameters.push((name, sort));
                    }
                    let d = self.declarations.get_mut(&id).unwrap();
                    d.input = field(node, "kind")
                        .is_some_and(|n| &self.source.text[n.byte_range()] == "input");
                    d.parameters = (!node.has_error()).then_some(parameters);
                }
                "statement" => self.rule(node, &scope),
                "domain" => {
                    if let Some(sort) = field(node, "sort")
                        .and_then(|n| self.reference(n, &scope, Lookup::Name(Kind::Sort)))
                    {
                        for n in node.children_by_field_name("value", &mut node.walk()) {
                            self.reference(
                                n,
                                &scope,
                                Lookup::Constant(Expected::Sort(sort.clone())),
                            );
                        }
                    }
                }
                "obligation" | "assumption" | "verification" => {
                    if let Some(n) = field(node, "name") {
                        self.declare(n, &scope, Kind::Contract, None, previous);
                    }
                    if node.kind() == "verification" {
                        let mut names = |key, kind| {
                            node.children_by_field_name(key, &mut node.walk())
                                .filter_map(|n| {
                                    self.reference(n, &scope, Lookup::Contract(kind))
                                        .map(|name| (name, n.byte_range()))
                                })
                                .collect()
                        };
                        let assumptions = names("assumption", ContractKind::Assumption);
                        let obligations: Vec<_> = names("obligation", ContractKind::Obligation);
                        if node
                            .children_by_field_name("obligation", &mut node.walk())
                            .next()
                            .is_none()
                            && !node.has_error()
                            && !node.is_missing()
                        {
                            self.issues.push(Issue {
                                span: field(node, "name").map_or(node.byte_range(), |n| n.byte_range()),
                                code: "consistency-only".into(),
                                message: "No obligations selected; this is a consistency-only verification.".into(),
                                warning: true,
                            });
                        }
                        self.verifications.push(VerificationReferences {
                            scope: scope.clone(),
                            assumptions,
                            obligations,
                        });
                    }
                    for card in node
                        .named_children(&mut node.walk())
                        .filter(|n| n.kind() == "cardinality")
                    {
                        if node.kind() == "assumption"
                            && field(card, "kind")
                                .is_some_and(|n| &self.source.text[n.byte_range()] != "at_most_one")
                        {
                            self.issues.push(Issue {
                                span: node.byte_range(),
                                code: "assumption-kind".into(),
                                message: format!(
                                    "{} is supported only for obligations",
                                    &self.source.text[field(card, "kind").unwrap().byte_range()]
                                ),
                                warning: false,
                            });
                        }
                        if let Some(rel) = field(card, "relation")
                            .and_then(|n| self.reference(n, &scope, Lookup::Name(Kind::Relation)))
                        {
                            for n in card.children_by_field_name("column", &mut card.walk()) {
                                self.reference(n, &scope, Lookup::Parameter(rel.clone()));
                            }
                        }
                    }
                }
                "source_location" | "location_alias" => {
                    if let Some(n) = field(node, "name") {
                        self.declare(n, &scope, Kind::Alias, None, previous);
                    }
                }
                _ => {}
            }
            if !matches!(node.kind(), "namespace" | "module" | "ERROR") {
                self.aliases(node, &scope);
            }
        }
    }
    fn aliases(&mut self, node: Node<'_>, scope: &Scope) {
        if node.kind() == "alias" && !self.references.iter().any(|r| r.span == node.byte_range()) {
            self.reference(node, scope, Lookup::Name(Kind::Alias));
        } else {
            for n in node.named_children(&mut node.walk()) {
                self.aliases(n, scope);
            }
        }
    }
    fn rule(&mut self, node: Node<'_>, scope: &Scope) {
        let mut tokens = vec![];
        leaves(&self.source, node, &mut tokens);
        let key = serde_json::to_string(&(
            ast::namespace_key(&scope.namespace),
            tokens
                .iter()
                .filter(|t| !t.comment)
                .map(|t| &t.text)
                .collect::<Vec<_>>(),
        ))
        .unwrap();
        let mut ordinal = 0;
        let id = loop {
            let id = format!("{key}#{ordinal}");
            if !self.rules.contains_key(&id) {
                break id;
            }
            ordinal += 1;
        };
        let mut atoms = vec![];
        let mut relations = vec![];
        let mut anchors = BTreeMap::new();
        let mut complete = !node.has_error();
        for outer in node.named_children(&mut node.walk()) {
            let role = match outer.kind() {
                "atom" => Role::Head,
                "positive_atom" => Role::Positive,
                "negative_atom" => Role::Negative,
                _ => continue,
            };
            let atom = if role == Role::Negative {
                outer
                    .named_children(&mut outer.walk())
                    .find(|n| n.kind() == "atom")
            } else {
                Some(outer)
            };
            let Some(atom) = atom else {
                continue;
            };
            let Some(n) = field(atom, "name") else {
                continue;
            };
            let Some(relation) = self.reference(n, scope, Lookup::Name(Kind::Relation)) else {
                complete = false;
                continue;
            };
            let atom_id = format!("atom{}", atoms.len());
            anchors.insert(atom_id.clone(), atom.byte_range());
            let mut variables = vec![];
            for term in atom
                .named_children(&mut atom.walk())
                .filter(|t| t.id() != n.id() && t.kind() != "comment")
            {
                let index = variables.len();
                let term_id = format!("{atom_id}/arg{index}");
                let lookup = match term.kind() {
                    "variable" => Lookup::Variable {
                        rule: id.clone(),
                        occurrence: term_id.clone(),
                    },
                    "anonymous" => Lookup::Anonymous(Expected::Argument(relation.clone(), index)),
                    _ => Lookup::Constant(Expected::Argument(relation.clone(), index)),
                };
                let name = self.reference(term, scope, lookup);
                if name.is_none() {
                    complete = false;
                }
                let variable = if term.kind() == "variable" {
                    anchors.insert(term_id.clone(), term.byte_range());
                    name.map(|n| NamedDeclaration {
                        id: term_id,
                        name: n.text,
                    })
                } else {
                    None
                };
                variables.push(variable);
            }
            atoms.push(RuleAtom {
                id: atom_id,
                relation: relation.spelling(),
                role,
                variables,
            });
            relations.push(relation);
        }
        self.rule_anchors.insert(id.clone(), anchors);
        self.rules.insert(
            id.clone(),
            Rule {
                syntax: RuleSyntax {
                    id,
                    complete,
                    atoms,
                },
                scope: scope.clone(),
                relations,
            },
        );
    }
    pub fn scope_at(&self, byte: usize) -> Scope {
        self.scopes
            .iter()
            .rev()
            .find(|(r, _)| r.start <= byte && byte <= r.end)
            .map(|(_, s)| s.clone())
            .unwrap_or_default()
    }
    pub fn reference_at(&self, byte: usize) -> Option<&Reference> {
        self.references
            .iter()
            .find(|r| r.span.start <= byte && byte < r.span.end)
    }
    /// Current CST tokens supply completion even for unfinished argument lists.
    pub fn completion_context(&self, byte: usize) -> Option<(Lookup, Scope, Range<usize>)> {
        if self
            .tokens
            .iter()
            .any(|t| t.comment && t.span.start <= byte && byte <= t.span.end)
        {
            return None;
        }
        // List delimiters survive parser recovery, including an unfinished
        // qualified reference. Replace the whole list member, not just its last
        // token, so completing `lib::` cannot insert a second namespace prefix.
        let tokens = self
            .tokens
            .iter()
            .filter(|t| !t.comment)
            .collect::<Vec<_>>();
        if let Some(open) = tokens
            .iter()
            .rposition(|t| t.span.end <= byte && t.text == "[")
        {
            let label = open.checked_sub(2).map(|i| tokens[i].text.as_str());
            let kind = match label {
                Some("assumptions") => Some(ContractKind::Assumption),
                Some("obligations") => Some(ContractKind::Obligation),
                _ => None,
            };
            if let Some(kind) = kind.filter(|_| tokens[open - 1].text == ":") {
                let after = &tokens[open + 1..];
                if !after
                    .iter()
                    .any(|t| t.span.end <= byte && matches!(t.text.as_str(), "]" | ";" | "{" | "}"))
                {
                    let member = after
                        .iter()
                        .rposition(|t| t.span.end <= byte && t.text == ",")
                        .map_or(0, |i| i + 1);
                    let name = after[member..]
                        .iter()
                        .take_while(|t| !matches!(t.text.as_str(), "," | "]" | ";" | "{" | "}"))
                        .collect::<Vec<_>>();
                    let span = match (name.first(), name.last()) {
                        (Some(first), Some(last)) if first.span.start <= byte => {
                            first.span.start..last.span.end
                        }
                        _ => byte..byte,
                    };
                    return Some((Lookup::Contract(kind), self.scope_at(byte), span));
                }
            }
        }
        if let Some(r) = self.reference_at(byte.saturating_sub(1)).filter(|r| {
            !matches!(
                r.lookup,
                Lookup::Declaration(_) | Lookup::Variable { .. } | Lookup::Anonymous(_)
            )
        }) {
            return Some((r.lookup.clone(), r.scope.clone(), r.span.clone()));
        }
        let current = self.tokens.iter().find(|t| {
            t.span.start <= byte
                && byte <= t.span.end
                && t.text
                    .chars()
                    .all(|c| c.is_alphanumeric() || "_'$:".contains(c))
        });
        let span = current.map_or(byte..byte, |t| t.span.clone());
        let before: Vec<_> = self
            .tokens
            .iter()
            .filter(|t| !t.comment && t.span.end <= span.start)
            .collect();
        let boundary = before
            .iter()
            .rposition(|t| matches!(t.text.as_str(), ";" | "{" | "}"))
            .map_or(0, |i| i + 1);
        let statement = &before[boundary..];
        let scope = self.scope_at(byte);
        if statement.first().is_some_and(|t| t.text == "use") {
            return Some((Lookup::Name(Kind::Namespace), scope, span));
        }
        if statement.first().is_some_and(|t| {
            matches!(
                t.text.as_str(),
                "relation" | "input" | "const" | "sort" | "namespace" | "module"
            )
        }) {
            return statement
                .last()
                .filter(|t| t.text == ":")
                .map(|_| (Lookup::Name(Kind::Sort), scope, span));
        }
        if statement
            .first()
            .is_some_and(|t| matches!(t.text.as_str(), "obligation" | "assumption"))
        {
            if let Some(card) = statement.windows(2).position(|ts| {
                matches!(
                    ts[0].text.as_str(),
                    "at_most_one" | "at_least_one" | "exactly_one" | "empty"
                ) && ts[1].text == "("
            }) {
                let args = &statement[card + 2..];
                if !args.iter().any(|t| t.text == ",") {
                    return Some((Lookup::Name(Kind::Relation), scope, span));
                }
                if statement[card].text != "empty" && args.iter().any(|t| t.text == "group_by") {
                    let relation = parse_name(&args.first()?.text).ok()?;
                    return Some((Lookup::Parameter(relation), scope, span));
                }
            }
        }
        if let Some(open) = statement.iter().rposition(|t| t.text == "(") {
            if open > 0 && !statement[open + 1..].iter().any(|t| t.text == ")") {
                let index = statement[open + 1..]
                    .iter()
                    .filter(|t| t.text == ",")
                    .count();
                let token = statement[open - 1];
                let node = self
                    .tree
                    .root_node()
                    .descendant_for_byte_range(token.span.start, token.span.end)?;
                let relation = decoded(&self.source, node, false)?;
                return Some((
                    Lookup::Constant(Expected::Argument(relation, index)),
                    scope,
                    span,
                ));
            }
        }
        Some((Lookup::Name(Kind::Relation), scope, span))
    }
}
