//! 6.0 evidence, not production semantic identity or an incremental checker.
//! Textual structural keys deliberately avoid arena IDs and global helper names.
use crate::*;
use denotate_editor::Document;
use denotate_ir::*;
use denotate_normalize::Instruction;
use denotate_test_dsl::{
    ast::{Expr, ExprKind, Program},
    lowering::{self, LoweredProgram, LoweringOutcome, projection, recipe::Recipe},
    syntax,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

type Entities = BTreeMap<String, String>;
type Inventory = BTreeMap<&'static str, Entities>;

fn parse(text: &str) -> (Program, Sources) {
    let mut sources = Sources::new();
    let id = sources
        .add("file:///inventory.inputmapping", 1, "test-dsl", text)
        .unwrap();
    let doc = Document::new(&mut syntax::parser().unwrap(), text.into(), 1, true);
    let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &sources, id).unwrap() else {
        panic!("invalid syntax in inventory fixture: {text}")
    };
    (ast, sources)
}

fn lower(text: &str) -> (Program, Sources, LoweredProgram) {
    let (ast, sources) = parse(text);
    let LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
        panic!("invalid names in inventory fixture: {text}")
    };
    (ast, sources, p)
}

fn constraints(p: &LoweredProgram) -> Vec<InputAtMostOne> {
    vec![InputAtMostOne {
        relation: p.library.value,
        group_by: vec![0],
    }]
}
fn prepare(p: &LoweredProgram, limits: &Limits) -> std::result::Result<GroundProgram, CheckError> {
    GroundProgram::prepare_with_input_groups(&p.corpus, &p.domains(), &constraints(p), limits)
}

struct Names {
    constants: BTreeMap<ConstantId, String>,
    relations: BTreeMap<RelationId, String>,
    rules: BTreeMap<RuleId, String>,
}
impl Names {
    fn new(ast: &Program, sources: &Sources, p: &LoweredProgram) -> Self {
        let c = &p.corpus;
        let constants = c
            .constants()
            .map(|v| {
                (
                    v.id,
                    format!("{:?}:{:?}", c.sort(v.sort).unwrap().name, v.name),
                )
            })
            .collect();
        let mut relations: BTreeMap<_, _> = c
            .relations()
            .filter(|r| !c.is_generated_relation(r.id))
            .map(|r| (r.id, format!("named:{:?}", r.name)))
            .collect();
        let mut helpers = c.relations().filter(|r| c.is_generated_relation(r.id));
        let mut installed = c.rules();
        let mut rules = BTreeMap::new();
        for head in [
            p.library.supplies,
            p.library.available,
            p.library.present,
            p.library.slot_value,
        ] {
            let rule = installed.next().unwrap();
            assert_eq!(
                rule.head.relation(),
                head,
                "library identity inventory needs review"
            );
            rules.insert(rule.id, format!("library:{}", relations[&head]));
        }
        for statement in projection::project(ast, sources).unwrap().statements {
            let owner = format!(
                "{:?}/duplicate:{}",
                statement.key.form, statement.key.duplicate
            );
            let recipe = Recipe::lower(statement.key.form).unwrap();
            if let Some(recipe) = recipe.normalized {
                for instruction in recipe.instructions() {
                    match instruction {
                        Instruction::Helper { id } => {
                            let r = helpers.next().unwrap();
                            relations.insert(r.id, format!("{owner}/helper:{}", id.0));
                        }
                        Instruction::Rule { id, .. } => {
                            rules.insert(
                                installed.next().unwrap().id,
                                format!("{owner}/rule:{}", id.0),
                            );
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(helpers.next().is_none() && installed.next().is_none());
        Self {
            constants,
            relations,
            rules,
        }
    }
    fn atom(&self, a: &Atom) -> String {
        let args: Vec<_> = a
            .arguments()
            .iter()
            .map(|v| match v.value() {
                Term::Constant(c) => self.constants[c].clone(),
                Term::Variable { name, .. } => format!("variable:{name}"),
            })
            .collect();
        format!("{}({args:?})", self.relations[&a.relation()])
    }
    fn ground(&self, a: &GroundAtom) -> String {
        let args: Vec<_> = a.arguments.iter().map(|c| &self.constants[c]).collect();
        format!("{}({args:?})", self.relations[&a.relation])
    }
    fn rule(&self, r: &GroundRule) -> String {
        let body: Vec<_> = r
            .body
            .iter()
            .map(|l| (format!("{:?}", l.polarity), self.ground(&l.term.atom)))
            .collect();
        format!("{} :- {body:?}", self.ground(&r.head.atom))
    }
    fn ground_key(&self, r: &GroundRule) -> String {
        // All grounded arguments include body-only substitutions. Rule/source
        // form changes are removal+addition, never guessed identity matches.
        format!("{} / {}", self.rules[&r.source], self.rule(r))
    }
}

fn inventory(ast: &Program, sources: &Sources, p: &LoweredProgram, g: &GroundProgram) -> Inventory {
    let n = Names::new(ast, sources, p);
    let mut out = Inventory::new();
    out.insert(
        "sorts",
        p.corpus
            .sorts()
            .map(|s| (s.name.clone(), s.name.clone()))
            .collect(),
    );
    out.insert(
        "constants",
        n.constants
            .values()
            .map(|c| (c.clone(), c.clone()))
            .collect(),
    );
    out.insert(
        "relations",
        p.corpus
            .relations()
            .map(|r| {
                let sorts: Vec<_> = r
                    .parameters
                    .iter()
                    .map(|v| &p.corpus.sort(v.sort).unwrap().name)
                    .collect();
                (
                    n.relations[&r.id].clone(),
                    format!("{:?}:{sorts:?}", r.role),
                )
            })
            .collect(),
    );
    out.insert(
        "rules",
        p.corpus
            .rules()
            .map(|r| {
                let body: Vec<_> = r
                    .body
                    .iter()
                    .map(|l| (matches!(l, Literal::Negative(_)), n.atom(l.atom())))
                    .collect();
                (
                    n.rules[&r.id].clone(),
                    format!("{} :- {body:?}", n.atom(&r.head)),
                )
            })
            .collect(),
    );
    out.insert(
        "possible_atoms",
        g.atoms()
            .map(|a| {
                let a = n.ground(a);
                (a.clone(), a)
            })
            .collect(),
    );
    let instances: BTreeMap<_, _> = g.rules().map(|r| (r.id, n.ground_key(r))).collect();
    out.insert(
        "ground_instances",
        g.rules()
            .map(|r| (instances[&r.id].clone(), n.rule(r)))
            .collect(),
    );
    let members: BTreeMap<_, _> = g
        .components()
        .map(|c| {
            let atoms: BTreeSet<_> = c.atoms.iter().map(|a| n.ground(a)).collect();
            (c.id, format!("{atoms:?}"))
        })
        .collect();
    out.insert(
        "components",
        g.components()
            .map(|c| {
                let rules: BTreeSet<_> = g.component_rules[c.id.index]
                    .iter()
                    .map(|i| &instances[&g.rules[*i].id])
                    .collect();
                let providers: BTreeSet<_> = c.dependencies.iter().map(|d| &members[d]).collect();
                (
                    members[&c.id].clone(),
                    format!(
                        "rules:{rules:?}; providers:{providers:?}; recursive:{}; negative:{}",
                        c.recursive,
                        c.cycle.is_some()
                    ),
                )
            })
            .collect(),
    );
    let mut groups = Entities::new();
    let mut cones = Entities::new();
    // Include trivial and empty groups: the runtime intentionally stores only
    // nontrivial groups. Empty roots still need producer/domain dependencies.
    for obligation in p.corpus.obligations() {
        let Requirement::AtMostOne { relation, group_by } = &obligation.requirement;
        let mut tuples = BTreeMap::<Vec<ConstantId>, Vec<GroundAtom>>::new();
        for a in g.atoms().filter(|a| a.relation == *relation) {
            tuples
                .entry(group_by.iter().map(|i| a.arguments[*i]).collect())
                .or_default()
                .push(a.clone());
        }
        // This inventory's one library obligation is grouped by Slot.
        assert_eq!(
            (*relation, group_by.as_slice()),
            (p.library.supplies, &[1][..])
        );
        for slot in p.corpus.constants().filter(|c| c.sort == p.library.slot) {
            tuples.entry(vec![slot.id]).or_default();
        }
        for (key, roots) in tuples {
            let key = format!(
                "{}:{:?}",
                obligation.name,
                key.iter().map(|c| &n.constants[c]).collect::<Vec<_>>()
            );
            let cone = g
                .dependency_cone(roots.clone(), &Limits::default())
                .unwrap();
            let facts: BTreeSet<_> = cone.facts.iter().map(|a| n.ground(a)).collect();
            let rules: BTreeSet<_> = cone.rules.iter().map(|r| &instances[r]).collect();
            let comps: BTreeSet<_> = cone.components.iter().map(|c| &members[c]).collect();
            let roots: BTreeSet<_> = roots.iter().map(|a| n.ground(a)).collect();
            groups.insert(key.clone(), format!("{roots:?}"));
            cones.insert(
                key,
                format!("roots:{roots:?}; facts:{facts:?}; rules:{rules:?}; components:{comps:?}"),
            );
        }
    }
    out.insert("obligation_groups", groups);
    out.insert("cones", cones);
    let inputs: BTreeSet<_> = g.input_atoms().map(|a| n.ground(a)).collect();
    out.insert(
        "input_context",
        BTreeMap::from([(
            "value-worlds".into(),
            format!("at-most-one-input:{inputs:?}"),
        )]),
    );
    out
}

fn delta(before: &Inventory, after: &Inventory) -> Value {
    before.iter().map(|(kind, old)| {
        let new = &after[kind];
        let added = new.keys().filter(|k| !old.contains_key(*k)).count();
        let removed = old.keys().filter(|k| !new.contains_key(*k)).count();
        let modified = old.iter().filter(|(k,v)| new.get(*k).is_some_and(|n| n != *v)).count();
        let unchanged = old.len() - removed - modified;
        let union = old.len() + added;
        ((*kind).into(), json!({"before":old.len(),"after":new.len(),"added":added,"removed":removed,"modified":modified,"unchanged":unchanged,"changed_over_union":[added+removed+modified,union]}))
    }).collect::<serde_json::Map<String, Value>>().into()
}

fn snapshot(text: &str) -> std::result::Result<Inventory, Vec<String>> {
    let (ast, sources) = parse(text);
    match lowering::lower(&ast, &sources).unwrap() {
        LoweringOutcome::UserErrors(errors) => {
            Err(errors.iter().map(|e| format!("{:?}", e.kind)).collect())
        }
        LoweringOutcome::Lowered(p) => {
            let g = prepare(&p, &Limits::default()).unwrap();
            Ok(inventory(&ast, &sources, &p, &g))
        }
    }
}

fn edit_cases() -> Vec<(String, String, String)> {
    let decl = "input i, j, k; slot a, b, c;\n";
    let a = "a <- i when input_value(i) is 1 and (present(j) or present(k));\n";
    let b = "a <- j;\nb <- k;\nc <- i when available(b);\n";
    let base = format!("{decl}{a}{b}");
    let inserted = "b <- i when present(j) and (present(i) or present(k));\n";
    let mut cases = vec![];
    let mut push = |name: &str, from: String, to: String| cases.push((name.into(), from, to));
    push("comment", base.clone(), format!("// moved source\n{base}"));
    push("numeric_alias", base.clone(), base.replace("is 1", "is 01"));
    push(
        "insert_helper_before",
        base.clone(),
        format!("{decl}{inserted}{a}{b}"),
    );
    push(
        "delete_statement",
        base.clone(),
        format!("{decl}{a}b <- k;\nc <- i when available(b);\n"),
    );
    push(
        "change_guard",
        base.clone(),
        base.replace("present(j) or present(k)", "present(j) and present(k)"),
    );
    push(
        "add_literal",
        base.clone(),
        format!("{base}mask b when input_value(k) is 2;\n"),
    );
    push(
        "remove_literal",
        format!("{base}mask b when input_value(k) is 2;\n"),
        base.clone(),
    );
    let no_value = base.replace("input_value(i) is 1", "present(i)");
    push("first_literal", no_value, base.clone());
    push(
        "unused_input",
        base.clone(),
        base.replace("input i, j, k;", "input i, j, k, z;"),
    );
    push(
        "unused_slot",
        base.clone(),
        base.replace("slot a, b, c;", "slot a, b, c, z;"),
    );
    push(
        "rename_input",
        base.clone(),
        base.replace("i, j", "ii, j")
            .replace("<- i ", "<- ii ")
            .replace("(i)", "(ii)"),
    );
    push("reorder_statements", base.clone(), format!("{decl}{b}{a}"));
    push(
        "reorder_declarations",
        base.clone(),
        base.replace("input i, j, k;", "input k, j, i;"),
    );
    push("duplicate_insert", base.clone(), format!("{base}{a}"));
    push("duplicate_delete", format!("{base}{a}"), base.clone());
    push(
        "mask",
        base.clone(),
        format!("{base}mask b when present(j);\n"),
    );
    let broken = base.replace("(j)", "(missing)");
    push("name_error", base.clone(), broken.clone());
    push("repair", broken, base.clone());
    push("undo", format!("{decl}{inserted}{a}{b}"), base.clone());
    push("redo", base.clone(), format!("{decl}{inserted}{a}{b}"));
    let open = "input i, j; slot a, b; a <- i when available(b); b <- j;";
    let closed = "input i, j; slot a, b; a <- i when available(b); b <- j when available(a);";
    push(
        "scc_merge",
        format!("{open} a <- i;"),
        format!("{closed} a <- i;"),
    );
    push(
        "scc_split",
        format!("{closed} a <- i;"),
        format!("{open} a <- i;"),
    );
    push(
        "remove_last_support",
        format!("{closed} a <- i;"),
        closed.into(),
    );
    push(
        "unchanged_provider_meaning",
        base.clone(),
        base.replace("b <- k;", "b <- k when present(k);"),
    );
    let wide = (0..16)
        .map(|i| format!("slot s{i}; s{i} <- i; s{i} <- j;\n"))
        .collect::<String>();
    push(
        "wide_local_guard",
        format!("input i, j;\n{wide}"),
        format!(
            "input i, j;\n{}",
            wide.replace("s0 <- i;", "s0 <- i when present(j);")
        ),
    );
    let deep = workload("helper_chain", 16);
    push(
        "nested_local_guard",
        deep.clone(),
        deep.replacen("is 1", "is 0", 1),
    );
    cases
}

fn capture_edits() -> Value {
    Value::Array(edit_cases().into_iter().map(|(name,before,after)| {
        let old = snapshot(&before);
        let new = snapshot(&after);
        let changes = match (&old,&new) { (Ok(a),Ok(b)) => delta(a,b), _ => Value::Null };
        json!({"edit":name,"before_source":before,"after_source":after,"before_errors":old.err(),"after_errors":new.err(),"changes":changes})
    }).collect())
}

fn workload(family: &str, size: usize) -> String {
    let extra = if family == "distinct_literals" {
        (1..size).map(|i| format!(", g{i}")).collect::<String>()
    } else {
        String::new()
    };
    let mut text = format!("input i0, i1, i2, i3{extra};\nslot s0, s1, s2, s3;\n");
    for i in 0..4 {
        let mut expr = format!("input_value(i{i}) is 0 or input_value(i{i}) is 1");
        for step in 1..size {
            expr = match family {
                "duplicates" => format!("({expr}) and present(i{i})"),
                "distinct_literals" => format!("({expr}) and present(g{step})"),
                "helper_chain" => format!("present(i{i}) or not (present(i{i}) and ({expr}))"),
                _ => panic!(),
            };
        }
        text.push_str(&format!("s{i} <- i{i} when {expr};\n"));
    }
    text
}

fn depth(e: &Expr) -> usize {
    1 + match &e.kind {
        ExprKind::And(a, b) | ExprKind::Or(a, b) => depth(a).max(depth(b)),
        ExprKind::Group(a) | ExprKind::Not { operand: a, .. } => depth(a),
        _ => 0,
    }
}
fn shape(ast: &Program, p: &LoweredProgram) -> Value {
    fn chain(
        id: RelationId,
        edges: &BTreeMap<RelationId, BTreeSet<RelationId>>,
        memo: &mut BTreeMap<RelationId, usize>,
    ) -> usize {
        if let Some(n) = memo.get(&id) {
            return *n;
        }
        let n = 1 + edges[&id]
            .iter()
            .map(|next| chain(*next, edges, memo))
            .max()
            .unwrap_or(0);
        memo.insert(id, n);
        n
    }
    let mut max_body = 0;
    let mut distinct = 0;
    let mut repeated = 0;
    let mut positive_pivots = 0;
    let mut edges: BTreeMap<_, BTreeSet<_>> = p
        .corpus
        .relations()
        .filter(|r| p.corpus.is_generated_relation(r.id))
        .map(|r| (r.id, BTreeSet::new()))
        .collect();
    for r in p.corpus.rules().skip(4) {
        max_body = max_body.max(r.body.len());
        let values: BTreeSet<_> = r
            .body
            .iter()
            .map(|l| {
                format!(
                    "{}:{:?}:{:?}",
                    matches!(l, Literal::Negative(_)),
                    l.atom().relation(),
                    l.atom()
                        .arguments()
                        .iter()
                        .map(|a| a.value())
                        .collect::<Vec<_>>()
                )
            })
            .collect();
        distinct += values.len();
        repeated += r.body.len() - values.len();
        positive_pivots += r
            .body
            .iter()
            .filter(|l| matches!(l, Literal::Positive(_)))
            .count();
        if let Some(deps) = edges.get_mut(&r.head.relation()) {
            deps.extend(
                r.body
                    .iter()
                    .map(|l| l.atom().relation())
                    .filter(|id| p.corpus.is_generated_relation(*id)),
            );
        }
    }
    let mut memo = BTreeMap::new();
    let helper_depth = edges
        .keys()
        .map(|id| chain(*id, &edges, &mut memo))
        .max()
        .unwrap_or(0);
    json!({"authored_depth_including_groups":ast.mappings.iter().filter_map(|m|m.condition.as_ref()).map(depth).max().unwrap_or(0),"max_normalized_body":max_body,"distinct_literals_summed_per_rule":distinct,"duplicate_literals_summed_per_rule":repeated,"program_positive_pivots":positive_pivots,"helpers":edges.len(),"helper_chain_depth":helper_depth,"inputs":ast.declarations.iter().filter(|d|d.kind==denotate_test_dsl::ast::Kind::Input).map(|d|d.names.len()).sum::<usize>()})
}

fn resource(c: Inconclusive) -> Value {
    json!({"phase":c.phase,"resource":c.resource})
}
fn budget_result(text: &str, max_work: usize) -> Value {
    let (ast, sources, p) = lower(text);
    let n = Names::new(&ast, &sources, &p);
    let limits = Limits {
        max_work,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let result = (|| -> std::result::Result<Value, CheckError> {
        let g = prepare(&p, &limits)?.admit(&limits)?;
        let m = g.symbolic(&limits)?;
        let report = m.verify_at_most_one(&limits)?;
        let groups:Vec<_>=report.groups.iter().map(|g| match &g.outcome {
            VerifiedOutcome::Proved=>json!({"status":"proved"}),
            VerifiedOutcome::Unsupported=>json!({"status":"unsupported"}),
            VerifiedOutcome::Inconclusive(c)=>json!({"status":"inconclusive","cause":resource(*c)}),
            VerifiedOutcome::Counterexample(c)=>json!({"status":"counterexample","present":c.observation.present.iter().map(|a|n.ground(a)).collect::<BTreeSet<_>>(),"absent":c.observation.absent.iter().map(|a|n.ground(a)).collect::<BTreeSet<_>>() }),
        }).collect();
        let regions:Vec<_>=report.unresolved.iter().map(|r|json!({"outcome":format!("{:?}",r.outcome),"completion":match &r.completion {CompletionOutcome::NoContradiction=>"no_contradiction",CompletionOutcome::NoMeaning(_)=>"no_meaning",CompletionOutcome::Deferred{..}=>"deferred",CompletionOutcome::Inconclusive(_)=>"inconclusive"}})).collect();
        Ok(json!({"groups":groups,"regions":regions}))
    })();
    match result {
        Ok(v) => v,
        Err(CheckError::LimitExceeded { phase, resource }) => {
            json!({"status":"inconclusive","phase":phase,"resource":resource})
        }
        Err(e) => panic!("{e}"),
    }
}

fn baseline() -> Value {
    let programs = [
        "input i, j; slot a; a <- i; a <- j;",
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
        "input i, j; slot a, b; a <- i when not available(b); b <- j when not available(a); a <- j;",
        "input i; slot a; a <- i when not available(a);",
    ];
    let budgets:Vec<_>=programs.iter().flat_map(|text|[0,100,500,2000,20000].into_iter().map(move |max_work|json!({"source":text,"max_work":max_work,"result":budget_result(text,max_work)}))).collect();
    json!({"schema":1,"note":"Pre-6a frozen outputs. Structural inventory is test-only and does not establish production cache soundness. A changed statement form is removed+added. Components match by membership; groups/cones match by obligation and grouping key. Invalid snapshots have no semantic inventory. Input context is separate from structural cones. Resource fixtures use generous deadlines; no timings are frozen.","edits":capture_edits(),"budgets":budgets})
}

#[test]
fn inventory_reference_matches_pre_slice_6_capture() {
    let expected: Value =
        serde_json::from_str(include_str!("../../fixtures/SLICE-6.0-BASELINE.json")).unwrap();
    assert_eq!(baseline(), expected);
}

#[test]
fn inventory_keys_and_workload_shapes_are_checked() {
    let cases = edit_cases();
    for name in [
        "comment",
        "numeric_alias",
        "reorder_statements",
        "reorder_declarations",
    ] {
        let (_, a, b) = cases.iter().find(|c| c.0 == name).unwrap();
        assert_eq!(snapshot(a).unwrap(), snapshot(b).unwrap(), "{name}");
    }
    let (_, a, b) = cases
        .iter()
        .find(|c| c.0 == "insert_helper_before")
        .unwrap();
    let old = snapshot(a).unwrap();
    let new = snapshot(b).unwrap();
    assert!(
        old["rules"]
            .iter()
            .all(|(k, v)| new["rules"].get(k) == Some(v))
    );
    let (_, a, b) = cases.iter().find(|c| c.0 == "scc_merge").unwrap();
    let (_, _, before) = lower(a);
    let (_, _, after) = lower(b);
    let before = prepare(&before, &Limits::default()).unwrap();
    let after = prepare(&after, &Limits::default()).unwrap();
    assert!(!before.components().any(|c| c.recursive));
    assert!(after.components().any(|c| c.recursive));
    assert_eq!(before.atoms().count(), after.atoms().count());
    let (_, a, b) = cases.iter().find(|c| c.0 == "remove_last_support").unwrap();
    let (_, _, before) = lower(a);
    let (_, _, after) = lower(b);
    assert!(
        prepare(&before, &Limits::default())
            .unwrap()
            .rules()
            .count()
            > prepare(&after, &Limits::default()).unwrap().rules().count()
    );
    for family in ["duplicates", "distinct_literals", "helper_chain"] {
        let (ast, sources, p) = lower(&workload(family, 16));
        let shape = shape(&ast, &p);
        if family == "helper_chain" {
            assert!(shape["helper_chain_depth"].as_u64().unwrap() > 4);
            assert!(shape["max_normalized_body"].as_u64().unwrap() <= 3);
        } else {
            assert_eq!(shape["helper_chain_depth"], 1);
            assert_eq!(shape["max_normalized_body"], 16);
            assert_eq!(
                shape["duplicate_literals_summed_per_rule"]
                    .as_u64()
                    .unwrap()
                    > 0,
                family == "duplicates"
            );
        }
        let g = prepare(&p, &Limits::default()).unwrap();
        let (profiled, _) = GroundProgram::profile_preparation(
            &p.corpus,
            &p.domains(),
            &constraints(&p),
            &Limits::default(),
        )
        .unwrap();
        assert_eq!(
            inventory(&ast, &sources, &p, &g),
            inventory(&ast, &sources, &p, &profiled)
        );
    }
}

#[test]
fn unchanged_provider_fixture_preserves_available_meaning() {
    let cases = edit_cases();
    let (_, a, b) = cases
        .iter()
        .find(|c| c.0 == "unchanged_provider_meaning")
        .unwrap();
    let (a_ast, a_sources, a) = lower(a);
    let (b_ast, b_sources, b) = lower(b);
    let an = Names::new(&a_ast, &a_sources, &a);
    let bn = Names::new(&b_ast, &b_sources, &b);
    let limits = Limits::default();
    let ag = prepare(&a, &limits).unwrap();
    let bg = prepare(&b, &limits).unwrap();
    let b_inputs: BTreeMap<_, _> = bg
        .input_atoms()
        .map(|v| (bn.ground(v), v.clone()))
        .collect();
    let available = |p: &LoweredProgram| {
        GroundAtom::new(
            p.library.available,
            [p.corpus
                .constants()
                .find(|c| c.sort == p.library.slot && c.name == "b")
                .unwrap()
                .id],
        )
    };
    let mut valid = 0;
    for world in super::rewrites::subsets(&ag.input_atoms().cloned().collect::<Vec<_>>()) {
        let Ok(ar) = ag.evaluate(world.clone(), &limits) else {
            continue;
        };
        let br = bg
            .evaluate(
                world.iter().map(|v| b_inputs[&an.ground(v)].clone()),
                &limits,
            )
            .unwrap();
        assert_eq!(
            format!("{:?}", ar.fact(&available(&a)).unwrap()),
            format!("{:?}", br.fact(&available(&b)).unwrap())
        );
        valid += 1;
    }
    assert_eq!(valid, 27);
}

#[test]
#[ignore = "manual pre-6a baseline capture; do not regenerate after changing contracts"]
fn capture_incremental_inventory() {
    println!("SLICE_60_BASELINE={}", baseline());
}

#[test]
#[ignore = "manual release 6.0 preparation probe"]
fn measure_preparation_shapes() {
    assert!(!cfg!(debug_assertions));
    let mut rows = vec![];
    for family in ["duplicates", "distinct_literals", "helper_chain"] {
        for size in [1, 4, 16, 64] {
            let source = workload(family, size);
            let (ast, sources, p) = lower(&source);
            let limits = Limits::default();
            let mut samples = vec![];
            let mut outcome = Value::Null;
            for iteration in 0..6 {
                let start = Instant::now();
                let g = prepare(&p, &limits).unwrap();
                let preparation_ns = start.elapsed().as_nanos();
                let grounding_ns = g.metrics().grounding.as_nanos();
                let graph_ns = g.metrics().admissibility.as_nanos();
                let start = Instant::now();
                let g = g.admit(&limits).unwrap();
                let admission_ns = start.elapsed().as_nanos();
                let start = Instant::now();
                let m = g.symbolic(&limits).unwrap();
                let symbolic_ns = start.elapsed().as_nanos();
                let start = Instant::now();
                let report = m.verify_at_most_one(&limits).unwrap();
                let verification_ns = start.elapsed().as_nanos();
                outcome = json!({"proved":report.all_obligations_proved(),"input_tuples":g.input_atoms().count(),"possible_atoms":g.atoms().count(),"ground_rules":g.rules().count(),"components":g.components().count(),"dependencies":g.dependencies.len(),"w_nodes":m.context().permitted_worlds().node_count()});
                if iteration > 0 {
                    samples.push(json!({"preparation_ns":preparation_ns,"grounding_ns":grounding_ns,"graph_ns":graph_ns,"admission_ns":admission_ns,"symbolic_ns":symbolic_ns,"verification_ns":verification_ns}));
                }
            }
            let (profiled, profile) = GroundProgram::profile_preparation(
                &p.corpus,
                &p.domains(),
                &constraints(&p),
                &limits,
            )
            .unwrap();
            let fresh = prepare(&p, &limits).unwrap();
            assert_eq!(
                inventory(&ast, &sources, &p, &fresh),
                inventory(&ast, &sources, &p, &profiled)
            );
            rows.push(json!({"family":family,"parameter":size,"source":source,"shape":shape(&ast,&p),"samples":samples,"outcome":outcome,"diagnostic_profile":{"work":profile.work,"calls":profile.calls,"segments_ns":profile.segments_ns}}));
        }
    }
    println!(
        "SLICE_60_GROWTH={}",
        json!({"note":"One warm-up + five measured samples on the normal public path with counters disabled; separate instrumented diagnostic run is not a latency sample. Test-only profile executes the same stage functions and is checked against the public preparation structurally. No optimization or caching. Default limits; every timing is local evidence, not a gate.","rows":rows})
    );
}
