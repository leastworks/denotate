//! Test-only interchange for the Python/Z3 comparison, not an IR wire format.
use denotate_check::*;
use denotate_ir::*;
use denotate_test_dsl::library;
use serde_json::{Value, json};

fn main() {
    println!(
        "{}",
        json!(
            [
                "overlap",
                "exclusive_inputs",
                "seeded_cycle",
                "unseeded_cycle"
            ]
            .map(case)
        )
    );
}
fn case(mode: &str) -> Value {
    let mut c = Corpus::new();
    let lib = library::build(&mut c).unwrap();
    let a = c.declare_constant("a", lib.slot).unwrap();
    let b = c.declare_constant("b", lib.slot).unwrap();
    let ia = c.declare_constant("input_a", lib.input).unwrap();
    let ib = c.declare_constant("input_b", lib.input).unwrap();
    let ibb = c.declare_constant("input_bb", lib.input).unwrap();
    let head = c.atom(lib.mapped_to, [ia.into(), a.into()]).unwrap();
    c.add_rule(head, []).unwrap();
    for input in [ib, ibb] {
        let head = c.atom(lib.mapped_to, [input.into(), b.into()]).unwrap();
        let guard = if mode == "exclusive_inputs" {
            let atom = c.atom(lib.present, [ia.into()]).unwrap();
            if input == ib {
                Literal::Positive(atom)
            } else {
                Literal::Negative(atom)
            }
        } else {
            let slot = if mode == "unseeded_cycle" || mode == "seeded_cycle" && input == ibb {
                b
            } else {
                a
            };
            Literal::Positive(c.atom(lib.available, [slot.into()]).unwrap())
        };
        c.add_rule(head, [guard]).unwrap();
    }
    let limits = Limits::default();
    let p = GroundProgram::prepare(
        &c,
        &Domains::from([(lib.slot, vec![a, b]), (lib.input, vec![ia, ib, ibb])]),
        &limits,
    )
    .unwrap();
    let meaning = p.symbolic(&limits).unwrap();
    let report = meaning.verify_at_most_one(&limits).unwrap();
    assert!(report.whole_program_admitted());
    let ground = |atom: &GroundAtom| json!({"name": c.relation(atom.relation).unwrap().name, "args": atom.arguments.iter().map(|id| c.constant(*id).unwrap().name.as_str()).collect::<Vec<_>>()});
    let atom = |atom: &Atom| json!({"name": c.relation(atom.relation()).unwrap().name, "args": atom.arguments().iter().map(|arg| match arg.value() { Term::Constant(id) => json!({"const": c.constant(*id).unwrap().name}), Term::Variable { name, .. } => json!({"var": name}) }).collect::<Vec<_>>()});
    let inputs: Vec<_> = p.input_atoms().cloned().collect();
    let worlds: Vec<_> = (0..1usize << inputs.len()).map(|bits| {
        let present: Vec<_> = inputs.iter().enumerate().filter(|(i, _)| bits & (1 << i) != 0).map(|(_, a)| a.clone()).collect();
        let replay = p.evaluate(present.clone(), &limits).unwrap();
        for fact in p.atoms() {
            let SymbolicFact::Settled(condition) = meaning.fact(fact).unwrap() else { panic!() };
            assert_eq!(meaning.context().evaluate(&condition, present.clone(), &limits).unwrap(), replay.fact(fact).unwrap() == FactState::Settled(true));
        }
        json!({"present": present.iter().map(&ground).collect::<Vec<_>>(), "derived": replay.established_facts().filter(|a| c.relation(a.relation).unwrap().role == RelationRole::Derived).map(&ground).collect::<Vec<_>>()})
    }).collect();
    let witnesses: Vec<_> = report
        .groups
        .iter()
        .filter_map(|g| match &g.outcome {
            VerifiedOutcome::Counterexample(e) => Some(
                e.observation
                    .present
                    .iter()
                    .map(&ground)
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .collect();
    json!({
        "case": mode,
        "domains": c.sorts().map(|s| (s.name.clone(), json!(c.constants().filter(|v| v.sort == s.id).map(|v| v.name.as_str()).collect::<Vec<_>>()))).collect::<serde_json::Map<_, _>>(),
        "predicates": c.relations().map(|r| (r.name.clone(), json!({"sorts": r.parameters.iter().map(|p| c.sort(p.sort).unwrap().name.as_str()).collect::<Vec<_>>(), "input": r.role == RelationRole::Input}))).collect::<serde_json::Map<_, _>>(),
        "rules": c.rules().map(|r| json!({"head": atom(&r.head), "body": r.body.iter().map(|l| json!({"negative": matches!(l, Literal::Negative(_)), "atom": atom(l.atom())})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "claim_pairs": [[ground(&GroundAtom::new(lib.supplies, [ib, b])), ground(&GroundAtom::new(lib.supplies, [ibb, b]))]],
        "worlds": worlds,
        "status": if witnesses.is_empty() { "proved" } else { "counterexample" },
        "witnesses": witnesses,
    })
}
