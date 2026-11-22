use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::*;
use denotate_ir_text::*;
use std::collections::{BTreeMap, BTreeSet};

fn load_text(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn export(p: &LoadedProgram, graph: &GroundProgram) -> String {
    let mut bytes = Vec::new();
    committed::write_committed(
        &mut bytes,
        &p.corpus,
        graph,
        p.corpus.verifications().next().unwrap(),
        &committed::Metadata {
            source_digest: "test",
            checker_commit: "test",
            round: 1,
            state: "test",
        },
        &Default::default(),
    )
    .unwrap();
    String::from_utf8(bytes).unwrap()
}
fn admitted(p: &LoadedProgram) -> GroundProgram {
    let l = Limits::default();
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let mut session = Session::default();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &l).unwrap();
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &(&l).into(), &fixed)
        .unwrap()
    else {
        panic!()
    };
    g.admit(&(&l).into()).unwrap().program().clone()
}
fn atom_name(p: &LoadedProgram, a: &GroundAtom) -> String {
    let r = p.corpus.relation(a.relation).unwrap();
    format!(
        "{:?}::{}({:?})",
        p.corpus.namespace(r.id).unwrap().segments(),
        r.name,
        a.arguments
            .iter()
            .map(|id| {
                let c = p.corpus.constant(*id).unwrap();
                (p.corpus.namespace(*id).unwrap().segments(), &c.name)
            })
            .collect::<Vec<_>>()
    )
}

// Independent GL-reduct oracle. Only negative-body truth is guessed; the
// reduct's positive least model then fixes all other atoms, including helpers.
fn models(rules: &[&GroundRule], world: &BTreeSet<GroundAtom>) -> BTreeSet<BTreeSet<GroundAtom>> {
    let negative = rules
        .iter()
        .flat_map(|r| &r.body)
        .filter(|l| l.polarity == Polarity::Negative)
        .map(|l| l.term.atom.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    assert!(negative.len() <= 16, "tiny oracle only: {}", negative.len());
    let mut result = BTreeSet::new();
    for mask in 0..1usize << negative.len() {
        let guess = negative
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, a)| a)
            .collect::<BTreeSet<_>>();
        let reduct = rules
            .iter()
            .filter(|r| {
                !r.body
                    .iter()
                    .any(|l| l.polarity == Polarity::Negative && guess.contains(&l.term.atom))
            })
            .collect::<Vec<_>>();
        let mut least = world.clone();
        loop {
            let before = least.len();
            for r in &reduct {
                assert!(
                    r.replacements.is_empty(),
                    "oracle runs on freshly loaded source"
                );
                if r.body
                    .iter()
                    .filter(|l| l.polarity == Polarity::Positive)
                    .all(|l| least.contains(&l.term.atom))
                {
                    least.insert(r.head.atom.clone());
                }
            }
            if before == least.len() {
                break;
            }
        }
        if negative
            .iter()
            .all(|a| guess.contains(a) == least.contains(a))
        {
            result.insert(least);
        }
    }
    result
}
fn permitted(p: &LoadedProgram, graph: &GroundProgram, world: &BTreeSet<GroundAtom>) -> bool {
    let v = p.corpus.verifications().next().unwrap();
    let assumptions = v
        .assumptions
        .iter()
        .map(|id| &p.corpus.assumption(*id).unwrap().restriction)
        .collect::<Vec<_>>();
    let mut cone = graph
        .atoms()
        .filter(|a| assumptions.iter().any(|r| r.relation() == a.relation))
        .cloned()
        .collect::<BTreeSet<_>>();
    loop {
        let before = cone.len();
        for r in graph.rules() {
            if cone.contains(&r.head.atom) {
                cone.extend(r.body.iter().map(|l| l.term.atom.clone()));
            }
        }
        if cone.len() == before {
            break;
        }
    }
    let rules = graph
        .rules()
        .filter(|r| cone.contains(&r.head.atom))
        .collect::<Vec<_>>();
    let meaning = models(&rules, world);
    assert_eq!(
        meaning.len(),
        1,
        "independent assumption cone must have one meaning"
    );
    let meaning = meaning.first().unwrap();
    assumptions.iter().all(|r| {
        let tuples = meaning
            .iter()
            .filter(|a| a.relation == r.relation())
            .collect::<Vec<_>>();
        if r.kind() == Cardinality::Empty {
            return tuples.is_empty();
        }
        let relation = p.corpus.relation(r.relation()).unwrap();
        let mut groups = vec![vec![]];
        for col in r.group_by() {
            groups = groups
                .iter()
                .flat_map(|g| {
                    p.domains[&relation.parameters[*col].sort].iter().map(|k| {
                        let mut g = g.clone();
                        g.push(*k);
                        g
                    })
                })
                .collect();
        }
        groups.iter().all(|g| {
            let count = tuples
                .iter()
                .filter(|a| {
                    r.group_by()
                        .iter()
                        .zip(g)
                        .all(|(col, value)| a.arguments[*col] == *value)
                })
                .count();
            match r.kind() {
                Cardinality::AtMostOne => count <= 1,
                Cardinality::AtLeastOne => count >= 1,
                Cardinality::ExactlyOne => count == 1,
                _ => unreachable!(),
            }
        })
    })
}
fn oracle(source: &LoadedProgram, reloaded: &LoadedProgram) {
    let l = Limits::default();
    let raw = GroundProgram::prepare(&source.corpus, &source.domains, &l).unwrap();
    let resumed = GroundProgram::prepare(&reloaded.corpus, &reloaded.domains, &l).unwrap();
    let inputs = raw
        .input_atoms()
        .map(|a| (atom_name(source, a), a))
        .collect::<BTreeMap<_, _>>();
    let next_inputs = resumed
        .input_atoms()
        .map(|a| (atom_name(reloaded, a), a))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        inputs.keys().collect::<Vec<_>>(),
        next_inputs.keys().collect::<Vec<_>>(),
        "input universe"
    );
    assert!(inputs.len() <= 10);
    let names = raw
        .atoms()
        .map(|a| atom_name(source, a))
        .collect::<BTreeSet<_>>();
    for mask in 0..1usize << inputs.len() {
        let world = inputs
            .values()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, a)| (*a).clone())
            .collect();
        let next_world = next_inputs
            .values()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, a)| (*a).clone())
            .collect();
        let allowed = permitted(source, &raw, &world);
        assert_eq!(
            allowed,
            permitted(reloaded, &resumed, &next_world),
            "W must be equal, including previously forbidden worlds"
        );
        if !allowed {
            continue;
        }
        let project = |p: &LoadedProgram, models: BTreeSet<BTreeSet<GroundAtom>>| {
            models
                .into_iter()
                .map(|m| {
                    m.iter()
                        .map(|a| atom_name(p, a))
                        .filter(|n| names.contains(n))
                        .collect::<BTreeSet<_>>()
                })
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(
            project(source, models(&raw.rules().collect::<Vec<_>>(), &world)),
            project(
                reloaded,
                models(&resumed.rules().collect::<Vec<_>>(), &next_world)
            ),
            "stable models, world {mask}"
        );
    }
}

#[test]
fn committed_export_preserves_exact_worlds_and_projected_stable_models() {
    let cases = [
        // Guarded replacement, jointly certified under disjoint signed guards.
        "input x(); relation a(); relation b(); a() :- x(), !b(); b() :- !x(), !a();",
        // Nonconstant shared expressions from a four-way joint certificate.
        "input x(); input y(); relation g0(); relation g1(); relation g2(); relation g3();
         g0() :- x(); g0() :- y(); g1() :- !x(); g1() :- y(); g2() :- x(); g2() :- !y(); g3() :- !x(); g3() :- !y();
         relation a0(); relation a1(); relation a2(); relation a3();
         a0() :- g0(), !a1(); a1() :- g1(), !a2(); a2() :- g2(), !a3(); a3() :- g3(), !a0();",
        // A redundant producer and its unreachable positive cycle are removed.
        "input x(); relation a(); relation b(); a() :- x(); a() :- x(), !b(); b() :- !a();",
    ];
    for (i, text) in cases.iter().enumerate() {
        let p = load_text(&format!(
            "{text} verification checks {{ assumptions: []; obligations: []; }}"
        ));
        let graph = admitted(&p);
        assert!(graph.is_admitted());
        assert!(
            graph.rewrite_proofs().count() > 0,
            "case {i} must exercise committed changes"
        );
        if i == 1 {
            assert!(
                graph
                    .rewrite_proofs()
                    .filter_map(|p| p.guarded_settlement())
                    .any(|p| matches!(p.certificate, GuardedCertificate::Joint(_)))
            );
        }
        if i == 2 {
            assert!(graph.residual_rules().count() < graph.original_residual_rules().count());
        }
        let text = export(&p, &graph);
        assert_eq!(text, export(&p, &graph), "deterministic export");
        oracle(&p, &load_text(&text));
    }
    let p = load_text(
        "input x(); input y(); relation good(); good() :- x(), !y();
        assumption required: at_least_one(good, group_by: ()); obligation no_y: empty(y);
        verification checks { assumptions: [required]; obligations: [no_y]; }",
    );
    let graph = admitted(&p);
    assert!(graph.rewrite_proofs().any(|p| p.is_redundant_negation()));
    oracle(&p, &load_text(&export(&p, &graph)));
}

#[test]
fn committed_export_keeps_domains_fixed_truth_eligibility_and_unrelated_cycles() {
    let p = load_text("namespace n { sort S; const a,b,c: S; domain S = [a,b];
        relation eligible(s:S); eligible(a); input x(s:S) within eligible;
        relation fixed(s:S); fixed(a); relation impossible(s:S); impossible(X) :- fixed(X), !fixed(X);
        relation a(); relation b(); a() :- !b(); b() :- !a();
        obligation coverage: at_least_one(fixed, group_by: (s));
        verification checks { assumptions: []; obligations: [coverage]; } }");
    let graph = admitted(&p);
    assert!(!graph.is_admitted());
    assert!(graph.fixed_size().1 > 0);
    let q = load_text(&export(&p, &graph));
    oracle(&p, &q);
    let sort = q.corpus.sorts().next().unwrap();
    assert_eq!(q.domains[&sort.id].len(), 2);
    assert_eq!(q.corpus.constants().count(), 3);
    assert!(!admitted(&q).is_admitted());
}

#[test]
fn committed_assumption_copies_do_not_duplicate_unreachable_ground_cycles() {
    let p = load_text(
        "sort S; const a,b:S; input present(s:S); input guarded(s:S);
        relation gives(s:S); gives(b); relation holds(s:S); relation supplied(s:S);
        holds(X) :- present(X); holds(X) :- guarded(X), !supplied(X);
        supplied(X) :- gives(X), !holds(X); relation broken(); broken() :- !holds(a);
        assumption valid: empty(broken); obligation o: empty(broken);
        verification checks { assumptions: [valid]; obligations: [o]; }",
    );
    let graph = admitted(&p);
    assert!(!graph.is_admitted());
    let q = load_text(&export(&p, &graph));
    oracle(&p, &q);
    assert_eq!(
        graph
            .residual_components()
            .filter(|c| c.cycle.is_some())
            .count(),
        admitted(&q)
            .residual_components()
            .filter(|c| c.cycle.is_some())
            .count(),
        "the unrelated cycle at b must not be duplicated into the assumption copy"
    );
}

#[test]
fn committed_round_stop_exports_after_both_commits_and_does_not_cache_partial_admission() {
    // First, subsume a redundant producer in one blocked cycle. In the same
    // round, a different mutually guarded pair receives a joint certificate.
    let p = load_text(
        "input x(); relation a(); relation b(); a() :- x(); a() :- x(), !b(); b() :- !a();
        relation c(); relation d(); c() :- x(), !d(); d() :- !x(), !c();
        verification checks { assumptions: []; obligations: []; }",
    );
    let l = Limits::default();
    let ops = (&l).into();
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let mut session = Session::default();
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &l).unwrap();
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    let events = std::cell::RefCell::new(Vec::new());
    let artifact = std::cell::RefCell::new(None);
    let dump = |e: AdmissionDump<'_>| {
        if let AdmissionDumpEvent::Graph { round, state, .. } = e.event {
            assert_eq!(round, 1);
            assert_eq!(state, "stopped");
            assert!(
                e.program
                    .rewrite_proofs()
                    .filter_map(|p| p.guarded_settlement())
                    .next()
                    .is_some()
            );
            *artifact.borrow_mut() = Some(export(&p, e.program));
        }
    };
    let result = g.admit_until_round(
        &ops,
        Some(&|e| events.borrow_mut().push(e.clone())),
        None,
        None,
        Some(&dump),
        Some(1),
    );
    assert!(matches!(
        result,
        Err(CheckError::StoppedAfterRound { round: 1 })
    ));
    let events = events.into_inner();
    assert!(events.iter().any(|e| e.stage == "structural-committed"));
    assert!(events.iter().any(|e| e.stage == "committed"));
    let q = load_text(&artifact.into_inner().unwrap());
    oracle(&p, &q);
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    let events = std::cell::RefCell::new(Vec::new());
    let g = g
        .admit_with_progress(&ops, Some(&|e| events.borrow_mut().push(e.clone())))
        .unwrap();
    assert!(events.borrow().iter().all(|e| e.stage != "reused"));
    assert_eq!(g.program().is_admitted(), admitted(&q).is_admitted());
    // Positive control: this preparation really has a shared admission cache.
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    let reused = std::cell::Cell::new(false);
    g.admit_with_progress(
        &ops,
        Some(&|e| reused.set(reused.get() || e.stage == "reused")),
    )
    .unwrap();
    assert!(reused.get());
    // An explicit stop must also bypass an already completed cache entry.
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    assert!(matches!(
        g.admit_until_round(&ops, None, None, None, None, Some(1)),
        Err(CheckError::StoppedAfterRound { round: 1 })
    ));
}

#[test]
fn committed_export_on_observer_cancellation_keeps_last_commit() {
    let p = load_text(
        "input x(); relation a(); relation b(); a() :- x(), !b(); b() :- !x(), !a(); verification checks { assumptions: []; obligations: []; }",
    );
    let l = Limits::default();
    let ops = OperationalLimits::from(&l);
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let RequestPreparation::Complete(g) = req.prepare(&p.corpus, &p.keys, &ops).unwrap() else {
        panic!()
    };
    let artifact = std::cell::RefCell::new(None);
    let observer = |e: &AdmissionProgress| {
        if e.stage == "committed" {
            ops.cancellation.cancel();
        }
    };
    let dump = |e: AdmissionDump<'_>| {
        if let AdmissionDumpEvent::Graph { .. } = e.event {
            *artifact.borrow_mut() = Some(export(&p, e.program));
        }
    };
    assert!(matches!(
        g.admit_with_diagnostics(&ops, Some(&observer), None, Some(&dump)),
        Err(CheckError::Cancelled)
    ));
    let q = load_text(
        &artifact
            .into_inner()
            .expect("last committed graph even on cancellation"),
    );
    oracle(&p, &q);
    assert_eq!(admitted(&p).is_admitted(), admitted(&q).is_admitted());
}

fn conclusions(p: &LoadedProgram, session: &mut Session) -> serde_json::Value {
    let l = Limits::default();
    let ops = (&l).into();
    let req = p.verification_requests(&l).unwrap().remove(0).1;
    let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &l).unwrap();
    let RequestPreparation::Complete(g) = session
        .prepare_with_fixed(&req, &p.corpus, &p.keys, &ops, &fixed)
        .unwrap()
    else {
        panic!()
    };
    let g = g.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&g, &ops).unwrap() else {
        panic!()
    };
    let results = &report.checked.results.value;
    let summary = denotate_presentation::summary(results);
    let emptiness = summary["emptiness"].as_array().into_iter().flatten().map(|v| serde_json::json!({"identity":v["identity"],"outcome":v["outcome"],"present":v["presentTuples"],"complete":v["complete"],"unresolved":v["unresolved"]})).collect::<Vec<_>>();
    let notices = results
        .notices
        .iter()
        .map(|(key, n)| (format!("{key:?}"), format!("{:?}", n.state)))
        .collect::<BTreeMap<_, _>>();
    serde_json::json!({"consistency":summary["consistency"],"groups":summary["groups"],"coverage":summary["coverage"],"emptiness":emptiness,"notices":notices})
}

#[test]
fn committed_zoo_obligation_and_notice_conclusions_agree_cold_and_warm() {
    let script =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/bench-den-zoo.mjs");
    let output = std::process::Command::new("node").args(["--input-type=module", "-e", "import {pathToFileURL} from 'node:url'; const m=await import(pathToFileURL(process.argv[1])); console.log(JSON.stringify(m.families.filter(f=>f!=='schema-layered').map(f=>[f,m.source(f,2,{ringLanes:1,ringRelays:2,ringReaders:1})])));"]).arg(script).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let sources: Vec<(String, String)> = serde_json::from_slice(&output.stdout).unwrap();
    for (name, text) in sources {
        let p = load_text(&text);
        // Committed admission export is a stable-semantics API. Completion zoo
        // families have separate grounding oracles and CLI smoke coverage.
        if p.corpus
            .verifications()
            .any(|v| v.options.semantics == Semantics::Completion)
        {
            continue;
        }
        let graph = admitted(&p);
        let q = load_text(&export(&p, &graph));
        let expected = conclusions(&p, &mut Session::default());
        let mut session = Session::default();
        assert_eq!(expected, conclusions(&q, &mut session), "cold {name}");
        assert_eq!(expected, conclusions(&q, &mut session), "warm {name}");
    }
    // Explicit coverage failures and all three conclusive notice states.
    let p = load_text("sort S; const a,b:S; relation r(s:S); r(a); input x(); relation yes(); yes(); relation no();
        obligation coverage: at_least_one(r, group_by: (s)); notice varies: varies(x); notice always: varies(yes); notice never: varies(no);
        verification checks { assumptions: []; obligations: [coverage]; notices: [varies,always,never]; }");
    let q = load_text(&export(&p, &admitted(&p)));
    assert_eq!(
        conclusions(&p, &mut Session::default()),
        conclusions(&q, &mut Session::default())
    );
}

#[test]
fn committed_export_preserves_the_declared_universe() {
    let p = load_text(
        "sort S; const a,b:S; relation eligible(x:S); eligible(a); eligible(b); input i(x:S) within eligible exactly_one(group_by:()); relation a(); relation b(); a():-i(a),!b(); b():-i(b),!a(); relation invalid(); invalid():-a(),b(); obligation ok:empty(invalid); verification v{assumptions:[];obligations:[ok];}",
    );
    let graph = admitted(&p);
    let source = export(&p, &graph);
    assert!(source.contains("exactly_one(group_by: ())"), "{source}");
    let q = load_text(&source);
    let restored = admitted(&q);
    assert!(!restored.input_universe_is_empty());
    let limits = Limits::default();
    let inputs = restored.input_atoms().cloned().collect::<Vec<_>>();
    assert_eq!(inputs.len(), 2);
    assert!(restored.evaluate([], &limits).is_err());
    assert!(restored.evaluate(inputs.clone(), &limits).is_err());
    for input in inputs {
        assert!(restored.evaluate([input], &limits).is_ok());
    }
}
