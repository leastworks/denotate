//! Shared regression corpora, key invariants, and current execution comparisons.
use denotate_check::*;
use denotate_editor::Document;
use denotate_ir::*;
use denotate_test_dsl::{
    ast::Program,
    lowering::{self, LoweredProgram, LoweringOutcome},
    syntax,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
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
    verification_constraints(&p.corpus, p.library.default_checks).unwrap()
}
fn prepare(p: &LoweredProgram, limits: &Limits) -> std::result::Result<GroundProgram, CheckError> {
    GroundProgram::prepare_with_input_groups(&p.corpus, &p.domains(), &constraints(p), limits)
}

struct Names<'a> {
    keys: &'a SemanticKeys,
}
impl<'a> Names<'a> {
    fn new(_ast: &Program, _sources: &Sources, p: &'a LoweredProgram) -> Self {
        Self { keys: &p.keys }
    }
    fn constant(c: &ConstantKey) -> String {
        format!("{:?}:{:?}", c.sort.0.name, c.name)
    }
    fn relation(r: &RelationKey) -> String {
        match r {
            RelationKey::Named(k) => format!("named:{:?}", k.name),
            RelationKey::Generated { owner, local } => format!(
                "{}/helper:{local}",
                std::str::from_utf8(owner.value()).unwrap()
            ),
        }
    }
    fn atom_key(a: &AtomKey) -> String {
        let args: Vec<_> = a.arguments.iter().map(Self::constant).collect();
        format!("{}({args:?})", Self::relation(&a.relation))
    }
    fn ground(&self, a: &GroundAtom) -> String {
        Self::atom_key(&AtomKey::from_atom(self.keys, a).unwrap())
    }
}

fn inventory(ast: &Program, sources: &Sources, p: &LoweredProgram, g: &GroundProgram) -> Inventory {
    let n = Names::new(ast, sources, p);
    let index = GroundKeyIndex::build(&p.corpus, &p.keys, g).unwrap();
    let mut out = Inventory::new();
    out.insert(
        "sorts",
        p.corpus
            .sorts()
            .map(|s| {
                let key = format!("{:?}", p.keys.sort(s.id).unwrap());
                (key.clone(), key)
            })
            .collect(),
    );
    out.insert(
        "constants",
        p.corpus
            .constants()
            .map(|c| {
                let key = format!("{:?}", p.keys.constant(c.id).unwrap());
                (key.clone(), key)
            })
            .collect(),
    );
    out.insert(
        "relations",
        p.corpus
            .relations()
            .map(|r| {
                (
                    format!("{:?}", p.keys.relation(r.id).unwrap()),
                    format!("{:?}", p.keys.relation_schema(r).unwrap()),
                )
            })
            .collect(),
    );
    out.insert(
        "rules",
        p.corpus
            .rules()
            .map(|r| {
                (
                    format!("{:?}", p.keys.rule(r.id).unwrap()),
                    format!("{:?}", p.keys.rule_schema(r).unwrap()),
                )
            })
            .collect(),
    );
    out.insert(
        "possible_atoms",
        g.atoms()
            .map(|a| {
                let key = format!("{:?}", index.atoms[a]);
                (key.clone(), key)
            })
            .collect(),
    );
    out.insert(
        "ground_instances",
        index
            .content
            .iter()
            .map(|(key, value)| (format!("{key:?}"), format!("{value:?}")))
            .collect(),
    );
    out.insert(
        "components",
        g.components()
            .map(|c| {
                let rules: BTreeSet<_> = denotate_check::test_support::component_rules(g, c.id)
                    .map(|r| &index.instances[&r.id])
                    .collect();
                let providers: BTreeSet<_> = c
                    .dependencies
                    .iter()
                    .map(|id| &index.components[id])
                    .collect();
                (
                    format!("{:?}", index.components[&c.id]),
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
    let current_atoms: BTreeMap<_, _> = index.atoms.iter().map(|(id, key)| (key, id)).collect();
    for (obligation, descriptor) in &index.groups {
        // The frontend library has one grouping column (Slot); empty groups
        // use the production domain descriptor, not corpus/name reconstruction.
        assert_eq!(descriptor.domains.len(), 1);
        for value in &descriptor.domains[0] {
            let key = descriptor.key(obligation, vec![value.clone()]).unwrap();
            let roots = descriptor
                .members
                .get(&key.tuple)
                .cloned()
                .unwrap_or_default();
            let cone = g
                .dependency_cone(
                    roots.iter().map(|a| (*current_atoms[a]).clone()),
                    &Limits::default(),
                )
                .unwrap();
            let facts: BTreeSet<_> = cone.facts.iter().map(|a| &index.atoms[a]).collect();
            let rules: BTreeSet<_> = cone.rules.iter().map(|r| &index.instances[r]).collect();
            let comps: BTreeSet<_> = cone
                .components
                .iter()
                .map(|c| &index.components[c])
                .collect();
            let key = format!("{key:?}");
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
    edit_regressions()
        .into_iter()
        .map(|row| {
            (
                row["edit"].as_str().unwrap().into(),
                row["before_source"].as_str().unwrap().into(),
                row["after_source"].as_str().unwrap().into(),
            )
        })
        .collect()
}

fn edit_regressions() -> Vec<Value> {
    let data: Value =
        serde_json::from_str(include_str!("../../fixtures/regression/edits.json")).unwrap();
    data["cases"].as_array().unwrap().clone()
}

fn regression_cases() -> Vec<Value> {
    let data: Value =
        serde_json::from_str(include_str!("../../fixtures/regression/outcomes.json")).unwrap();
    data["cases"].as_array().unwrap().clone()
}

// Resource limits are test inputs, never expected historical costs or outcomes.
// These four programs and limits preserve the old source/limit matrix; every
// semantic corpus case also runs with ample resources.
fn resource_cases() -> Vec<(String, usize)> {
    let mut cases: Vec<_> = regression_cases()
        .into_iter()
        .map(|r| {
            (
                r["source"].as_str().unwrap().to_owned(),
                Limits::default().max_work,
            )
        })
        .collect();
    for source in [
        "input i, j; slot a; a <- i; a <- j;",
        "input i, j; slot a; a <- i when input_value(i) is 1; a <- j when input_value(i) is 2;",
        "input i, j; slot a, b; a <- i when not available(b); b <- j when not available(a); a <- j;",
        "input i; slot a; a <- i when not available(a);",
    ] {
        for work in [0, 100, 500, 2000, 20000] {
            cases.push((source.into(), work));
        }
    }
    cases
}

// Derive search bounds from this execution, not a historical storage threshold.
fn condition_storage_peak(receipts: &WorkReceipts) -> usize {
    receipts
        .entries()
        .flat_map(|(_, r)| &r.own.resource_peaks)
        .filter(|(key, _)| key.resource == "condition nodes")
        .map(|(_, peak)| *peak)
        .max()
        .expect("fixture must retain conditions")
}

fn semantic_outcomes(mut report: Value) -> Value {
    if let Some(groups) = report["groups"].as_array_mut() {
        for group in groups {
            group.as_object_mut().unwrap().remove("present");
            group.as_object_mut().unwrap().remove("absent");
        }
    }
    report
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

fn resource(c: Inconclusive) -> Value {
    json!({"phase":c.phase,"resource":c.resource})
}

fn budget_result_lowered(p: &LoweredProgram, max_work: usize) -> Value {
    let n = Names { keys: &p.keys };
    let limits = Limits {
        max_work,
        timeout: Duration::from_secs(60),
        ..Limits::default()
    };
    let result = (|| -> std::result::Result<Value, CheckError> {
        let g = prepare(&p, &limits)?.admit(&limits)?;
        let m = g.symbolic(&limits)?;
        let report = m.verify_at_most_one(&limits)?;
        Ok(captured_report(&report, &n))
    })();
    match result {
        Ok(v) => v,
        Err(CheckError::LimitExceeded { phase, resource }) => {
            json!({"status":"inconclusive","phase":phase,"resource":resource})
        }
        Err(e) => panic!("{e}"),
    }
}

fn captured_report(report: &Verification<'_>, n: &Names<'_>) -> Value {
    let groups:Vec<_>=report.groups.iter().map(|g| match &g.outcome {
            VerifiedOutcome::Proved=>json!({"status":"proved"}),
            VerifiedOutcome::Unsupported=>json!({"status":"unsupported"}),
            VerifiedOutcome::Inconclusive(c)=>json!({"status":"inconclusive","cause":resource(*c)}),
            VerifiedOutcome::Counterexample(c)=>json!({"status":"counterexample","present":c.observation.present.iter().map(|a|n.ground(a)).collect::<BTreeSet<_>>(),"absent":c.observation.absent.iter().map(|a|n.ground(a)).collect::<BTreeSet<_>>() }),
        }).collect();
    let regions:Vec<_>=report.unresolved.iter().map(|r|json!({"outcome":format!("{:?}",r.outcome),"completion":match &r.completion {CompletionOutcome::NoContradiction=>"no_contradiction",CompletionOutcome::NoMeaning(_)=>"no_meaning",CompletionOutcome::Deferred{..}=>"deferred",CompletionOutcome::Inconclusive(_)=>"inconclusive"}})).collect();
    json!({"groups":groups,"regions":regions})
}

#[test]
fn edit_sources_preserve_validation_errors() {
    for row in edit_regressions() {
        for side in ["before", "after"] {
            let source = row[format!("{side}_source")].as_str().unwrap();
            assert_eq!(
                json!(snapshot(source).err()),
                row[format!("{side}_errors")],
                "{} / {side}",
                row["edit"]
            );
        }
    }
}

#[test]
fn inventory_keys_and_preparation_paths_agree() {
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

#[path = "key_evidence.rs"]
mod key_evidence;

#[path = "request_evidence.rs"]
mod request_evidence;

#[path = "budget_evidence.rs"]
mod budget_evidence;

#[path = "local.rs"]
mod local;

#[path = "memo.rs"]
mod memo;

#[path = "plans.rs"]
mod plans;

#[path = "owned.rs"]
mod owned;

#[path = "grounding.rs"]
mod grounding;
#[path = "sat.rs"]
mod sat;
