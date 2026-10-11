use super::*;

/// Head followed by body atoms in source order. None arguments are constants or
/// wildcards: neither has a rule-local variable identity.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct RuleSyntax {
    pub id: String,
    pub complete: bool,
    pub atoms: Vec<RuleAtom>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct RuleAtom {
    pub id: String,
    pub relation: String,
    pub role: Role,
    pub variables: Vec<Option<NamedDeclaration>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    Head,
    Positive,
    Negative,
}

#[salsa::input]
pub(super) struct RuleInput {
    pub syntax: RuleSyntax,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct RuleAnalysis {
    pub variables: Vec<Variable>,
    pub diagnostics: Vec<RuleDiagnostic>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Variable {
    pub name: String,
    /// First occurrence is the definition; all IDs are relative to this file.
    pub occurrences: Vec<String>,
    pub sorts: Vec<Symbol>,
    pub unknown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuleDiagnostic {
    pub id: String,
    pub code: String,
    pub message: String,
    pub warning: bool,
}

#[salsa::tracked]
pub(super) fn analyze_rule(
    db: &dyn Db,
    catalog: Catalog,
    file: File,
    rule: RuleInput,
) -> RuleAnalysis {
    db.record_query(QueryKind::Rules);
    let syntax = rule.syntax(db);
    let mut result = RuleAnalysis::default();
    let mut positive = std::collections::HashSet::new();
    let mut requiring = std::collections::HashSet::new();
    for atom in &syntax.atoms {
        if syntax.complete && atom.role == Role::Head {
            let matches: Vec<_> = visible_relations(db, catalog, file)
                .iter()
                .filter(|target| target.name == atom.relation)
                .collect();
            if let [target] = matches.as_slice() {
                if let Some(&owner) = visible_files(db, catalog, file)
                    .iter()
                    .find(|owner| owner.uri(db) == &target.uri)
                {
                    if owner.input_relations(db).contains(&target.id) {
                        result.diagnostics.push(RuleDiagnostic {
                            id: atom.id.clone(),
                            code: "input-definition".into(),
                            warning: false,
                            message: format!(
                                "Input relation '{}' cannot be defined by a fact or rule head.",
                                atom.relation
                            ),
                        });
                    }
                }
            }
        }
        for (index, term) in atom.variables.iter().enumerate() {
            let Some(term) = term else { continue };
            if atom.role == Role::Positive {
                positive.insert(term.name.clone());
            } else {
                requiring.insert(term.name.clone());
            }
            let variable_index = result
                .variables
                .iter()
                .position(|v| v.name == term.name)
                .unwrap_or_else(|| {
                    result.variables.push(Variable {
                        name: term.name.clone(),
                        occurrences: vec![],
                        sorts: vec![],
                        unknown: false,
                    });
                    result.variables.len() - 1
                });
            let variable = &mut result.variables[variable_index];
            variable.occurrences.push(term.id.clone());
            match expected_argument_sort(db, catalog, file, atom.relation.clone(), index) {
                Some(sort) => {
                    if !variable.sorts.contains(sort) {
                        variable.sorts.push(sort.clone());
                    }
                }
                None => variable.unknown = true,
            }
        }
    }
    // Recovery may have lost a binding or another occurrence. Keep navigation
    // and known sort evidence, but do not diagnose from incomplete rule syntax.
    if syntax.complete {
        for variable in &result.variables {
            let unsafe_binding =
                requiring.contains(&variable.name) && !positive.contains(&variable.name);
            let issue = if unsafe_binding {
                Some((
                    "unsafe-variable",
                    false,
                    format!(
                        "Variable '{}' in the head or negation needs positive-body support.",
                        variable.name
                    ),
                ))
            } else if variable.occurrences.len() == 1 {
                Some((
                    "singleton-variable",
                    true,
                    format!(
                        "Variable '{}' occurs only once; check its spelling or use '_' if intentional.",
                        variable.name
                    ),
                ))
            } else {
                None
            };
            if let Some((code, warning, message)) = issue {
                result.diagnostics.push(RuleDiagnostic {
                    id: variable.occurrences[0].clone(),
                    code: code.into(),
                    warning,
                    message,
                });
            }
            if variable.sorts.len() > 1 {
                let mut labels: Vec<_> = variable
                    .sorts
                    .iter()
                    .map(|sort| format!("{}.{}", sort.module.as_deref().unwrap_or("?"), sort.name))
                    .collect();
                labels.sort();
                result.diagnostics.push(RuleDiagnostic {
                    id: variable.occurrences[0].clone(),
                    code: "variable-sort-conflict".into(),
                    warning: false,
                    message: format!(
                        "Variable '{}' has conflicting expected sorts: {}.",
                        variable.name,
                        labels.join(", ")
                    ),
                });
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(id: &str, relation: &str, role: Role, names: &[&str]) -> RuleAtom {
        RuleAtom {
            id: id.into(),
            relation: relation.into(),
            role,
            variables: names
                .iter()
                .enumerate()
                .map(|(i, name)| {
                    (*name != "_").then(|| NamedDeclaration {
                        id: format!("{id}/{i}"),
                        name: (*name).into(),
                    })
                })
                .collect(),
        }
    }
    fn rule(id: &str, atoms: Vec<RuleAtom>) -> RuleSyntax {
        RuleSyntax {
            id: id.into(),
            complete: true,
            atoms,
        }
    }
    fn document(rules: Vec<RuleSyntax>) -> Document {
        Document {
            uri: "example".into(),
            directory: "root".into(),
            filename: "example.den".into(),
            module: Some("example".into()),
            imports: vec![],
            sorts: ["A", "B"]
                .iter()
                .map(|name| NamedDeclaration {
                    id: (*name).into(),
                    name: (*name).into(),
                })
                .collect(),
            relations: ["r", "s"]
                .iter()
                .map(|name| NamedDeclaration {
                    id: (*name).into(),
                    name: (*name).into(),
                })
                .collect(),
            signatures: ["r", "s"]
                .iter()
                .map(|id| Signature {
                    id: (*id).into(),
                    parameters: Some(vec![Some("A".into())]),
                })
                .collect(),
            constants: vec![],
            input_relations: vec![],
            rules,
        }
    }
    fn codes(result: &RuleAnalysis) -> Vec<&str> {
        result.diagnostics.iter().map(|d| d.code.as_str()).collect()
    }

    #[test]
    fn safety_singletons_facts_and_anonymous_terms() {
        let mut core = Analysis::default();
        let mut doc = document(vec![rule(
            "rule",
            vec![
                atom("head", "r", Role::Head, &["D"]),
                atom("body", "s", Role::Positive, &["Ss"]),
            ],
        )]);
        core.update(doc.clone());
        assert_eq!(
            codes(&core.rule_analysis("example", "rule")),
            ["unsafe-variable", "singleton-variable"]
        );
        doc.rules[0].atoms[1] = atom("body", "s", Role::Positive, &["D"]);
        core.update(doc.clone());
        let result = core.rule_analysis("example", "rule");
        assert!(result.diagnostics.is_empty());
        assert_eq!(result.variables[0].occurrences, ["head/0", "body/0"]);
        doc.rules[0].atoms[1].role = Role::Negative;
        core.update(doc.clone());
        assert_eq!(
            codes(&core.rule_analysis("example", "rule")),
            ["unsafe-variable"]
        );
        doc.rules[0].atoms.pop(); // Nonground fact.
        core.update(doc.clone());
        assert_eq!(
            codes(&core.rule_analysis("example", "rule")),
            ["unsafe-variable"]
        );
        doc.rules[0].atoms = vec![atom("body", "s", Role::Positive, &["_", "_"])];
        core.update(doc);
        assert!(core.rule_analysis("example", "rule").variables.is_empty());
    }

    #[test]
    fn recovery_and_unknown_sorts_do_not_invent_evidence() {
        let mut core = Analysis::default();
        let mut doc = document(vec![rule(
            "rule",
            vec![
                atom("head", "r", Role::Head, &["D"]),
                atom("body", "s", Role::Positive, &["D"]),
            ],
        )]);
        doc.signatures[1].parameters = Some(vec![Some("B".into())]);
        core.update(doc.clone());
        assert_eq!(
            codes(&core.rule_analysis("example", "rule")),
            ["variable-sort-conflict"]
        );
        doc.signatures[1].parameters = None;
        core.update(doc.clone());
        let result = core.rule_analysis("example", "rule");
        assert!(result.diagnostics.is_empty());
        assert!(result.variables[0].unknown);
        assert_eq!(result.variables[0].sorts[0].name, "A");
        doc.rules[0].atoms[1].variables[0].as_mut().unwrap().name = "Typo".into();
        doc.rules[0].complete = false;
        core.update(doc);
        let result = core.rule_analysis("example", "rule");
        assert!(result.diagnostics.is_empty());
        assert_eq!(
            result.variables.len(),
            2,
            "recovery preserves navigation identities"
        );
    }

    #[test]
    fn rule_inputs_are_independent_and_kind_changes_invalidate_checks_not_visibility() {
        let mut core = Analysis::default();
        let r = rule(
            "one",
            vec![
                atom("head", "r", Role::Head, &["D"]),
                atom("body", "s", Role::Positive, &["D"]),
            ],
        );
        let mut second = r.clone();
        second.id = "two".into();
        let mut doc = document(vec![r, second]);
        core.update(doc.clone());
        for id in ["one", "two"] {
            assert!(core.rule_analysis("example", id).diagnostics.is_empty());
        }
        let before = core.query_counts();
        core.update(doc.clone());
        core.rule_analysis("example", "one");
        assert_eq!(core.query_counts().rules, before.rules);
        doc.rules[0].atoms[1].variables[0].as_mut().unwrap().name = "Typo".into();
        core.update(doc.clone());
        core.rule_analysis("example", "one");
        core.rule_analysis("example", "two");
        assert_eq!(core.query_counts().rules, before.rules + 1);
        doc.input_relations.push("r".into());
        core.update(doc.clone());
        assert_eq!(
            codes(&core.rule_analysis("example", "two")),
            ["input-definition"]
        );
        assert_eq!(core.query_counts().relations, before.relations);
        doc.rules.remove(0);
        core.update(doc.clone());
        assert_eq!(
            core.rule_analysis("example", "one"),
            RuleAnalysis::default()
        );
        core.remove("example");
        assert_eq!(
            core.rule_analysis("example", "two"),
            RuleAnalysis::default()
        );
        core.update(doc);
        assert_eq!(
            codes(&core.rule_analysis("example", "two")),
            ["input-definition"]
        );
    }

    #[test]
    fn updating_and_removing_one_file_preserves_other_files_rule_inputs() {
        let mut core = Analysis::default();
        let syntax = rule(
            "same-id",
            vec![
                atom("head", "r", Role::Head, &["D"]),
                atom("body", "s", Role::Positive, &["D"]),
            ],
        );
        let mut first = document(vec![syntax.clone()]);
        let mut second = document(vec![syntax]);
        second.uri = "second".into();
        second.filename = "second.den".into();
        second.module = Some("second".into());
        core.update(first.clone());
        core.update(second);
        assert!(
            core.rule_analysis("second", "same-id")
                .diagnostics
                .is_empty()
        );
        let input = core.rules["second"]["same-id"];
        let before = core.query_counts().rules;
        first.rules.clear();
        core.update(first);
        assert!(core.rules["example"].is_empty());
        assert!(core.rules["second"]["same-id"] == input);
        assert!(
            core.rule_analysis("second", "same-id")
                .diagnostics
                .is_empty()
        );
        assert_eq!(core.query_counts().rules, before);
        core.remove("example");
        assert!(!core.rules.contains_key("example"));
        assert!(core.rules["second"]["same-id"] == input);
        assert!(
            core.rule_analysis("second", "same-id")
                .diagnostics
                .is_empty()
        );
        assert_eq!(core.query_counts().rules, before);
    }

    #[test]
    fn same_spelled_sorts_in_two_signature_modules_remain_distinct() {
        let mut core = Analysis::default();
        let mut left = document(vec![]);
        left.uri = "left".into();
        left.filename = "left.den".into();
        left.module = Some("left".into());
        left.relations.retain(|r| r.name == "r");
        let mut right = document(vec![]);
        right.uri = "right".into();
        right.filename = "right.den".into();
        right.module = Some("right".into());
        right.relations.retain(|r| r.name == "s");
        let mut caller = document(vec![rule(
            "one",
            vec![
                atom("head", "r", Role::Head, &["D"]),
                atom("body", "s", Role::Positive, &["D"]),
            ],
        )]);
        caller.relations.clear();
        caller.sorts.clear();
        caller.signatures.clear();
        caller.imports = vec![Some("left".into()), Some("right".into())];
        core.update(left);
        core.update(right);
        core.update(caller);
        let result = core.rule_analysis("example", "one");
        assert_eq!(codes(&result), ["variable-sort-conflict"]);
        assert!(result.diagnostics[0].message.contains("left.A, right.A"));
    }
}
