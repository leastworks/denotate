use denotate_check::{AtomKey, GroundAtom, Limits};
use denotate_ir_text::*;
use denotate_plan::{
    Options, Order, Output,
    completion::{Build, Next, Outcome, Plan, Planner, Problem, Terminal},
};
use std::collections::{BTreeMap, BTreeSet};
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///completion-plan.den", 1, text);
    load(&ProgramMembership::single("plan", [s.uri.clone()]), &[s]).unwrap()
}
const V: &str = "verification checks{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[];}";
fn atom(p: &LoadedProgram, name: &str) -> GroundAtom {
    GroundAtom::new(
        p.corpus.relations().find(|r| r.name == name).unwrap().id,
        [],
    )
}
fn key(p: &LoadedProgram, name: &str) -> AtomKey {
    AtomKey::from_atom(&p.keys, &atom(p, name)).unwrap()
}
fn build(p: &LoadedProgram, outputs: &[&str], opts: &Options) -> Build {
    Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        &Limits::default(),
        Default::default(),
    )
    .unwrap()
    .build(
        &outputs
            .iter()
            .map(|n| Output {
                atom: atom(p, n),
                priority: 0,
            })
            .collect::<Vec<_>>(),
        opts,
    )
    .unwrap()
}
fn ready(b: Build) -> Plan {
    match b {
        Build::Ready(p) => p,
        other => panic!("{other:?}"),
    }
}
#[test]
fn actual_raw_drives_rejection_and_processing_never_runs_after_reject() {
    let p = loaded(&format!(
        "input raw();relation h();h():-raw();relation out();out():-raw();{V}"
    ));
    let plan = ready(build(&p, &["out"], &Options::default()));
    assert!(matches!(plan.terminal(), Some(Terminal::Test(_))));
    for raw in [false, true] {
        for order in [
            Order::Semantic,
            Order::ReverseSemantic,
            Order::OutputPriority,
        ] {
            let e = plan
                .execute_permitted(&BTreeMap::from([(key(&p, "raw"), raw)]), order, 1000)
                .unwrap();
            assert_eq!(matches!(e.outcome, Outcome::Accepted { .. }), raw);
            if let Outcome::Accepted { outputs } = e.outcome {
                assert!(outputs[&key(&p, "out")]);
            } else {
                assert!(!e.trace.contains(&key(&p, "out")));
            }
        }
    }
    assert!(
        plan.execute_permitted(&BTreeMap::new(), Order::Semantic, 1000)
            .is_err()
    );
    assert!(
        plan.execute_permitted(
            &BTreeMap::from([(key(&p, "raw"), true)]),
            Order::Semantic,
            0
        )
        .is_err()
    );
    let json = plan.to_json();
    assert_eq!(json["version"], 5);
    assert_eq!(json["semantics"], "completion");
    // The accepted region hangs off the accepting leaf: processing follows
    // acceptance by construction.
    assert_eq!(json["plan"]["next"]["kind"], "leaf");
    assert_eq!(json["plan"]["next"]["terminal"]["kind"], "classify");
    assert!(json["plan"]["next"]["accepted"]["nodes"].is_array());
    assert_eq!(
        json,
        ready(build(&p, &["out"], &Options::default())).to_json()
    );
}
#[test]
fn hypothesis_settles_self_support_without_a_least_fixpoint_kernel() {
    let p = loaded(&format!("relation p();p():-p();relation h();h():-p();{V}"));
    let plan = ready(build(&p, &["p"], &Options::default()));
    // Under H, h and p are constant true and their definitions hold: no check.
    assert!(matches!(plan.terminal(), Some(Terminal::Test(_))));
    for order in [
        Order::Semantic,
        Order::ReverseSemantic,
        Order::OutputPriority,
    ] {
        let e = plan
            .execute_permitted(&BTreeMap::new(), order, 1000)
            .unwrap();
        assert!(matches!(e.outcome,Outcome::Accepted{outputs} if outputs[&key(&p,"p")]));
    }
    assert!(!plan.to_json().to_string().contains("least-fixpoint"));
}
#[test]
fn all_rejected_is_complete_and_outside_contradictions_do_not_reject() {
    let p = loaded(&format!("relation h();relation bad();bad():-!bad();{V}"));
    let plan = ready(build(&p, &["bad"], &Options::default()));
    assert_eq!(plan.terminal(), Some(&Terminal::Reject));
    assert!(matches!(
        plan.root().next,
        Next::Leaf { accepted: None, .. }
    ));
    assert!(matches!(
        plan.execute_permitted(&BTreeMap::new(), Order::Semantic, 100)
            .unwrap()
            .outcome,
        Outcome::Rejected
    ));
    let p = loaded(&format!(
        "input raw();relation h();h():-raw();relation out();out();relation bad();bad():-!bad();{V}"
    ));
    assert!(matches!(
        build(&p, &["out"], &Options::default()),
        Build::Ready(_)
    ));
    // No classification interpretation at all: every input is invalid and
    // rejects (024.38), rather than blocking the plan.
    let p = loaded(&format!("relation h();h():-!h();relation out();out();{V}"));
    assert_eq!(
        ready(build(&p, &["out"], &Options::default())).terminal(),
        Some(&Terminal::Reject)
    );
}
#[test]
fn output_scope_needs_existence_on_every_accepted_observation_and_explicit_determinacy() {
    // true is a conditional constant where p has a model; raw=true has none.
    let p = loaded(&format!(
        "input raw();relation h();h();relation p();p():-!raw();p():-raw(),!p();{V}"
    ));
    let b = build(&p, &["p"], &Options::default());
    // The raw = true arm reaches acceptance with no processing interpretation.
    assert!(
        matches!(b,Build::Problem(ref p) if matches!(**p,Problem::MeaningFailure{ref path} if path.len() == 1)),
        "{b:?}"
    );
    let p = loaded(&format!(
        "relation h();h();relation p();p():-p();relation out();out();{V}"
    ));
    assert!(matches!(
        build(&p, &["out"], &Options::default()),
        Build::Ready(_)
    ));
    // p :- p has two values and nothing to split on: unresolved, never guessed.
    assert!(
        matches!(build(&p,&["p"],&Options::default()),Build::Problem(p) if matches!(*p,Problem::Unresolved{phase:"processing",..}))
    );
}
#[test]
fn union_of_output_cones_is_checked_and_helpers_need_not_be_unique() {
    let p = loaded(&format!(
        "relation h();h();relation helper();helper():-helper();relation a();a():-helper();a():-!a();relation b();b():-!helper();b():-!b();{V}"
    ));
    assert!(matches!(
        build(&p, &["a"], &Options::default()),
        Build::Ready(_)
    ));
    assert!(matches!(
        build(&p, &["b"], &Options::default()),
        Build::Ready(_)
    ));
    assert!(
        matches!(build(&p,&["a","b"],&Options::default()),Build::Problem(p) if matches!(*p,Problem::MeaningFailure{..}))
    );
}
#[test]
fn no_hypothesis_and_finite_absent_outputs_use_completion_without_kernels() {
    let p = loaded(
        "sort S;const a,b:S;domain S=[b];relation out(x:S);verification checks{semantics:completion;decisions:[];assumptions:[];obligations:[];}",
    );
    let planner = Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        &Limits::default(),
        Default::default(),
    )
    .unwrap();
    let r = p.corpus.relations().next().unwrap().id;
    let outputs = planner.relation_outputs(r, 0).unwrap();
    assert_eq!(outputs.len(), 1);
    let plan = ready(planner.build(&outputs, &Options::default()).unwrap());
    assert_eq!(
        plan,
        ready(planner.build(&outputs, &Options::default()).unwrap())
    );
    assert!(
        matches!(plan.execute_permitted(&BTreeMap::new(),Order::Semantic,1000).unwrap().outcome,Outcome::Accepted{outputs} if outputs.values().all(|v| !v))
    );
}
#[test]
fn selected_assumptions_are_separate_from_rejection_and_invalid_contracts_block_plans() {
    let p = loaded(
        "input raw();relation h();h():-raw();relation out();out();assumption absent:empty(raw);verification checks{semantics:completion;hypothesis:h;decisions:[];assumptions:[absent];obligations:[];}",
    );
    assert_eq!(
        ready(build(&p, &["out"], &Options::default())).terminal(),
        Some(&Terminal::Reject)
    );
    let p = loaded(
        "input raw();relation h();h():-raw();relation out();out();assumption absent:empty(raw);assumption present:at_least_one(raw,group_by:());verification checks{semantics:completion;hypothesis:h;decisions:[];assumptions:[absent,present];obligations:[];}",
    );
    assert!(matches!(
        build(&p, &["out"], &Options::default()),
        Build::NoPermittedWorlds
    ));
    let p = loaded(
        "relation h();h();relation p();p():-p();relation out();out();assumption absent:empty(p);verification checks{semantics:completion;hypothesis:h;decisions:[];assumptions:[absent];obligations:[];}",
    );
    assert!(matches!(
        build(&p, &["out"], &Options::default()),
        Build::Problem(_)
    ));
}
#[test]
fn unresolved_mixed_cycles_and_resource_cutoffs_never_publish_partial_plans() {
    // A decision that varies under H with nothing to split on stays unresolved.
    let p = loaded(
        "relation p();p():-p();relation q();q():-q();relation h();h():-p();h():-q();relation out();out();verification checks{semantics:completion;hypothesis:h;decisions:[p];assumptions:[];obligations:[];}",
    );
    assert!(
        matches!(build(&p,&["out"],&Options::default()),Build::Problem(p) if matches!(*p,Problem::Unresolved{phase:"classification",..}))
    );
    // With no declared decision, H forces the helper loop and runtime checks keep
    // the actual acceptance test: raw rejects when false.
    let p = loaded(&format!(
        "input raw();relation p();p():-p();relation h();h():-raw(),p();relation out();out();{V}"
    ));
    let plan = ready(build(&p, &["out"], &Options::default()));
    for raw in [false, true] {
        let run = plan
            .execute_permitted(
                &BTreeMap::from([(key(&p, "raw"), raw)]),
                Order::Semantic,
                1000,
            )
            .unwrap();
        assert_eq!(matches!(run.outcome, Outcome::Accepted { .. }), raw);
    }
    let p = loaded(&format!(
        "input raw();relation h();h():-raw();relation out();out();{V}"
    ));
    for options in [
        Options {
            max_nodes: 0,
            ..Default::default()
        },
        Options {
            max_oracle_calls: 0,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            build(&p, &["out"], &options),
            Build::Inconclusive(_)
        ));
    }
}
#[test]
fn complete_plans_agree_with_independent_equation_enumeration_on_every_input() {
    let mut completed = 0;
    for left in 0..8 {
        for right in 0..8 {
            let equation = |head: &str, other: &str, kind| match kind {
                0 => String::new(),
                1 => format!("{head}();"),
                2 => format!("{head}():-{head}();"),
                3 => format!("{head}():-!{head}();"),
                4 => format!("{head}():-raw();"),
                5 => format!("{head}():-!raw();"),
                6 => format!("{head}():-{other}();"),
                _ => format!("{head}():-!{other}();"),
            };
            let p = loaded(&format!(
                "input raw();relation p();relation h();{}{}{V}",
                equation("p", "h", left),
                equation("h", "p", right)
            ));
            let result = build(&p, &["p"], &Options::default());
            let mut scope = BTreeSet::from([atom(&p, "h").relation]);
            loop {
                let mut next = scope.clone();
                for r in p
                    .corpus
                    .rules()
                    .filter(|r| scope.contains(&r.head.relation()))
                {
                    next.extend(r.body.iter().map(|l| l.atom().relation()));
                }
                if next == scope {
                    break;
                }
                scope = next;
            }
            let mut expected = Vec::new();
            for raw in [false, true] {
                let mut models = Vec::new();
                let mut classification_exists = false;
                let mut classification_accepts = false;
                for bits in 0..4 {
                    let values = BTreeMap::from([
                        (atom(&p, "raw").relation, raw),
                        (atom(&p, "p").relation, bits & 1 != 0),
                        (atom(&p, "h").relation, bits & 2 != 0),
                    ]);
                    let equation_holds = |id| {
                        values[&id]
                            == p.corpus
                                .rules()
                                .filter(|r| r.head.relation() == id)
                                .any(|r| {
                                    r.body.iter().all(|l| {
                                        values[&l.atom().relation()]
                                            == matches!(l, denotate_ir::Literal::Positive(_))
                                    })
                                })
                    };
                    let valid_class = ["p", "h"].iter().all(|n| {
                        let id = atom(&p, n).relation;
                        !scope.contains(&id) || equation_holds(id)
                    });
                    classification_exists |= valid_class;
                    classification_accepts |= valid_class && values[&atom(&p, "h").relation];
                    if ["p", "h"]
                        .iter()
                        .all(|n| equation_holds(atom(&p, n).relation))
                    {
                        models.push(values);
                    }
                }
                let accepted: Vec<_> = models
                    .iter()
                    .filter(|m| m[&atom(&p, "h").relation])
                    .collect();
                expected.push((
                    classification_exists,
                    classification_accepts,
                    accepted
                        .iter()
                        .map(|m| m[&atom(&p, "p").relation])
                        .collect::<BTreeSet<_>>(),
                ));
            }
            if let Build::Ready(plan) = result {
                completed += 1;
                for (raw, (_exists, accepts, outputs)) in [false, true].into_iter().zip(expected) {
                    // Inputs with no classification interpretation are invalid and
                    // must reject (024.38): `accepts` is false for them.
                    for order in [
                        Order::Semantic,
                        Order::ReverseSemantic,
                        Order::OutputPriority,
                    ] {
                        let run = plan
                            .execute_permitted(
                                &BTreeMap::from([(key(&p, "raw"), raw)]),
                                order,
                                10000,
                            )
                            .unwrap();
                        // Outcome first, before any output assertions.
                        assert_eq!(
                            matches!(run.outcome, Outcome::Accepted { .. }),
                            accepts,
                            "{left},{right},{raw}"
                        );
                        if let Outcome::Accepted { outputs: actual } = run.outcome {
                            assert_eq!(outputs, BTreeSet::from([actual[&key(&p, "p")]]));
                        }
                    }
                }
            } else {
                assert!(
                    !matches!(
                        result,
                        Build::Inconclusive(_) | Build::OracleInconclusive(_)
                    ),
                    "tiny defaults: {result:?}"
                );
            }
        }
    }
    assert!(
        completed > 20,
        "exercise successful plans as well as refusals"
    );
}

#[test]
fn direct_input_outputs_prepare_their_domains_without_changing_decisions() {
    for provider in ["eligible();", "eligible():-eligible();"] {
        let p = loaded(&format!(
            "relation eligible();{provider}input raw() within eligible;relation h();h();{V}"
        ));
        let b = build(&p, &["raw"], &Options::default());
        if provider == "eligible();" {
            let plan = ready(b);
            assert!(plan.inputs().contains(&key(&p, "raw")));
            for raw in [false, true] {
                let run = plan
                    .execute_permitted(
                        &BTreeMap::from([(key(&p, "raw"), raw)]),
                        Order::Semantic,
                        1000,
                    )
                    .unwrap();
                assert!(
                    matches!(run.outcome,Outcome::Accepted{outputs} if outputs[&key(&p,"raw")]==raw)
                );
            }
        } else {
            assert!(matches!(b,Build::Problem(p) if matches!(*p,Problem::InputDomains(_))));
        }
    }
}

#[test]
fn explicit_tuple_determinacy_does_not_require_its_siblings() {
    let p = loaded(
        "sort S;const a,b:S;relation h();h();relation out(x:S);out(a);out(b):-out(b);verification checks{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[];}",
    );
    let planner = Planner::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        p.corpus.verifications().next().unwrap().id,
        &Limits::default(),
        Default::default(),
    )
    .unwrap();
    let r = p.corpus.relations().find(|r| r.name == "out").unwrap().id;
    for name in ["a", "b", "a"] {
        let v = p.corpus.constants().find(|c| c.name == name).unwrap().id;
        let result = planner
            .build(
                &[Output {
                    atom: GroundAtom::new(r, [v]),
                    priority: 0,
                }],
                &Options::default(),
            )
            .unwrap();
        assert_eq!(matches!(result, Build::Ready(_)), name == "a");
    }
}

/// Brute force over nullary programs: for each input assignment, whether an
/// interpretation of C(H) with H exists, and the output's values over full
/// interpretations of the output and classification scopes with H.
fn semantic(
    p: &LoadedProgram,
    inputs: &[&str],
    output: &str,
) -> Vec<(BTreeMap<String, bool>, bool, BTreeSet<bool>)> {
    let names: Vec<String> = p.corpus.relations().map(|r| r.name.clone()).collect();
    let derived: Vec<String> = names
        .iter()
        .filter(|n| !inputs.contains(&n.as_str()))
        .cloned()
        .collect();
    let id = |n: &str| p.corpus.relations().find(|r| r.name == n).unwrap().id;
    let closure = |roots: &[&str]| {
        let mut scope: BTreeSet<_> = roots.iter().map(|n| id(n)).collect();
        loop {
            let mut next = scope.clone();
            for r in p
                .corpus
                .rules()
                .filter(|r| scope.contains(&r.head.relation()))
            {
                next.extend(r.body.iter().map(|l| l.atom().relation()));
            }
            if next == scope {
                return scope;
            }
            scope = next;
        }
    };
    let class = closure(&["h"]);
    let mut full = closure(&[output]);
    full.extend(class.iter().copied());
    let mut out = vec![];
    for bits in 0..1usize << inputs.len() {
        let world: BTreeMap<String, bool> = inputs
            .iter()
            .enumerate()
            .map(|(i, n)| (n.to_string(), bits & (1 << i) != 0))
            .collect();
        let mut accepts = false;
        let mut outputs = BTreeSet::new();
        for d in 0..1usize << derived.len() {
            let mut values: BTreeMap<_, bool> = world.iter().map(|(n, v)| (id(n), *v)).collect();
            for (i, n) in derived.iter().enumerate() {
                values.insert(id(n), d & (1 << i) != 0);
            }
            let holds = |r: denotate_ir::RelationId| {
                values[&r]
                    == p.corpus
                        .rules()
                        .filter(|x| x.head.relation() == r)
                        .any(|x| {
                            x.body.iter().all(|l| {
                                values[&l.atom().relation()]
                                    == matches!(l, denotate_ir::Literal::Positive(_))
                            })
                        })
            };
            if !values[&id("h")] {
                continue;
            }
            let derived_in = |scope: &BTreeSet<denotate_ir::RelationId>| {
                scope
                    .iter()
                    .filter(|r| !inputs.iter().any(|n| id(n) == **r))
                    .all(|r| holds(*r))
            };
            if derived_in(&class) {
                accepts = true;
                if derived_in(&full) {
                    outputs.insert(values[&id(output)]);
                }
            }
        }
        out.push((world, accepts, outputs));
    }
    out
}

#[test]
fn driver_plans_keep_the_outcome_invariant_on_every_input() {
    let programs = [
        // Guarded self-admission (k3b shape): H forces h and readable; their
        // definitions stay as runtime checks, so tag = false rejects.
        (
            "input tag();input g();relation h();relation readable();h():-tag(),readable();readable():-h();relation out();out():-g();",
            vec!["tag", "g"],
            "out",
        ),
        // x :- j; x :- i, !x: i, !j has no interpretation and must reject.
        (
            "input i();input j();input k();relation x();x():-j();x():-i(),!x();relation h();h():-!x(),k();relation out();out():-k();",
            vec!["i", "j", "k"],
            "out",
        ),
        // A guarded odd loop: s makes the input invalid.
        (
            "input s();relation a();a():-s(),!a();relation h();h():-!a();relation out();out():-a();",
            vec!["s"],
            "out",
        ),
        // A helper that varies under H: the driver splits on s.
        (
            "input s();relation a();a():-s(),a();relation h();h():-!s();h():-s(),a();relation out();out():-a();",
            vec!["s"],
            "out",
        ),
        // An output with two values under H when i holds: never a complete plan.
        (
            "input i();relation h();h():-i();relation p();p():-p(),i();p():-!i();",
            vec!["i"],
            "p",
        ),
    ];
    let mut ready_plans = 0;
    let mut split_plans = 0;
    for (text, inputs, output) in programs {
        let p = loaded(&format!("{text}{V}"));
        let expected = semantic(&p, &inputs, output);
        match build(&p, &[output], &Options::default()) {
            Build::Ready(plan) => {
                ready_plans += 1;
                split_plans += usize::from(plan.splits() > 0);
                for (world, accepts, outputs) in &expected {
                    let observed = world.iter().map(|(n, v)| (key(&p, n), *v)).collect();
                    let run = plan
                        .execute_permitted(&observed, Order::Semantic, 10_000)
                        .unwrap();
                    assert_eq!(
                        matches!(run.outcome, Outcome::Accepted { .. }),
                        *accepts,
                        "{text} at {world:?}"
                    );
                    if let Outcome::Accepted { outputs: actual } = run.outcome {
                        assert_eq!(
                            *outputs,
                            BTreeSet::from([actual[&key(&p, output)]]),
                            "{text} at {world:?}"
                        );
                    }
                }
            }
            other => {
                // A refusal is allowed only where an accepted input has no unique output.
                assert!(
                    expected.iter().any(|(_, a, o)| *a && o.len() != 1),
                    "{text}: {other:?}"
                );
            }
        }
    }
    assert_eq!(ready_plans, 4);
    assert!(split_plans >= 1);
}
