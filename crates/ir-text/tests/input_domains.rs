use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::*;
use denotate_ir_text::*;
use std::collections::BTreeSet;
mod support;

fn parse(text: &str) -> denotate_ir_text::Result<LoadedProgram> {
    let file = SourceFile::new("file:///program.den", 1, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
}
fn relation(p: &LoadedProgram, name: &str) -> RelationId {
    p.corpus.relations().find(|r| r.name == name).unwrap().id
}
fn atom(p: &LoadedProgram, name: &str, values: &[&str]) -> GroundAtom {
    GroundAtom::new(
        relation(p, name),
        values
            .iter()
            .map(|v| p.corpus.constants().find(|c| &c.name == v).unwrap().id),
    )
}
fn run(p: &LoadedProgram, session: &mut Session) -> (ScopedResults, BTreeSet<AtomKey>) {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let inputs = prepared
        .program()
        .input_atoms()
        .map(|a| AtomKey::from_atom(&p.keys, a).unwrap())
        .collect();
    let prepared = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &ops).unwrap() else {
        panic!()
    };
    (report.checked.results.value, inputs)
}
const BASE: &str = "sort S; const a,b:S; relation allowed(x:S); input i(x:S) within allowed;";
const CHECKS: &str = "obligation covered: at_least_one(i, group_by:x); obligation vacant: empty(i); verification checks { assumptions:[]; obligations:[covered,vacant]; }";

#[test]
fn exact_static_evaluation_includes_positive_recursion_and_stratified_negation() {
    let p = parse(&format!(
        "{BASE}
        relation candidate(x:S); relation blocked(x:S); relation reach(x:S);
        candidate(a); candidate(b); blocked(b);
        reach(a); reach(b); reach(X) :- allowed(X);
        allowed(X) :- candidate(X), !blocked(X), reach(X);
        {CHECKS}"
    ))
    .unwrap();
    let allowed = atom(&p, "i", &["a"]);
    let excluded = atom(&p, "i", &["b"]);
    let ground = GroundProgram::prepare(&p.corpus, &p.domains, &Limits::default()).unwrap();
    assert_eq!(
        ground.input_atoms().cloned().collect::<Vec<_>>(),
        [allowed.clone()]
    );
    for present in [vec![], vec![allowed.clone()]] {
        let replay = ground
            .evaluate(present.clone(), &Limits::default())
            .unwrap();
        assert_eq!(
            replay.fact(&allowed).unwrap(),
            FactState::Settled(!present.is_empty())
        );
        assert_eq!(replay.fact(&excluded).unwrap(), FactState::Settled(false));
    }
    assert!(matches!(
        ground.evaluate([excluded], &Limits::default()),
        Err(CheckError::InvalidObservation(_))
    ));
    let (results, inputs) = run(&p, &mut Session::default());
    assert_eq!(inputs.len(), 1);
    assert_eq!(results.coverage.values().next().unwrap().missing, 2);
    assert_eq!(results.emptiness.values().next().unwrap().present, 1);
}

#[test]
fn excluded_atoms_are_false_in_rules_and_absent_from_observations_but_kept_as_negative_evidence() {
    let p = parse(&format!(
        "{BASE} allowed(a);
        relation yes(); relation no(); yes() :- !i(b); no() :- i(b);
        obligation positive: empty(no); obligation negative: empty(yes);
        verification checks {{ assumptions:[]; obligations:[positive,negative]; }}"
    ))
    .unwrap();
    let ground = GroundProgram::prepare(&p.corpus, &p.domains, &Limits::default()).unwrap();
    for world in [vec![], vec![atom(&p, "i", &["a"])]] {
        let replay = ground.evaluate(world, &Limits::default()).unwrap();
        assert_eq!(
            replay.fact(&atom(&p, "yes", &[])).unwrap(),
            FactState::Settled(true)
        );
        assert_eq!(
            replay.fact(&atom(&p, "no", &[])).unwrap(),
            FactState::Settled(false)
        );
        let Evidence::Derived { premises, .. } =
            &replay.derivation(&atom(&p, "yes", &[])).unwrap().evidence
        else {
            panic!()
        };
        assert!(premises.iter().any(|e| matches!(e, PremiseEvidence::Absent { fact, provider: CompletedProvider::NoPossibleProducer, .. } if fact == &atom(&p,"i", &["b"]))));
    }
    let (results, inputs) = run(&p, &mut Session::default());
    let excluded = AtomKey::from_atom(&p.keys, &atom(&p, "i", &["b"])).unwrap();
    for result in results.emptiness.values() {
        for example in &result.examples {
            assert!(!example.observation.present.contains(&excluded));
            assert!(!example.observation.absent.contains(&excluded));
            assert_eq!(
                example
                    .observation
                    .present
                    .union(&example.observation.absent)
                    .cloned()
                    .collect::<BTreeSet<_>>(),
                inputs
            );
        }
    }
}

#[test]
fn empty_and_zero_arity_domains_and_coverage_keep_sort_groups() {
    let p = parse(&format!("{BASE}{CHECKS}")).unwrap();
    let (results, inputs) = run(&p, &mut Session::default());
    assert!(inputs.is_empty());
    let coverage = results.coverage.values().next().unwrap();
    assert!(coverage.complete());
    assert_eq!(coverage.missing, 2);
    assert!(!coverage.no_groups);
    assert!(results.emptiness.values().next().unwrap().proved());
    for (fact, count) in [("", 0), ("allowed();", 1)] {
        let p = parse(&format!("relation allowed(); input i() within allowed; {fact}
            obligation vacant: empty(i); verification checks {{ assumptions:[]; obligations:[vacant]; }}")).unwrap();
        let (results, inputs) = run(&p, &mut Session::default());
        assert_eq!(inputs.len(), count);
        assert_eq!(
            results.emptiness.values().next().unwrap().proved(),
            count == 0
        );
    }
}

#[test]
fn invalid_providers_are_located_at_the_reference() {
    for (declarations, rules, reason) in [
        ("input allowed(x:S);", "", "must be derived"),
        ("relation allowed();", "", "same arity"),
        ("sort T; relation allowed(x:T);", "", "positional sorts"),
        (
            "relation allowed(x:S); input other(x:S);",
            "allowed(X) :- other(X);",
            "depends on an input",
        ),
        (
            "relation allowed(x:S); relation mid(x:S);",
            "allowed(X) :- mid(X); mid(X) :- i(X);",
            "depends on an input",
        ),
        (
            "relation allowed(x:S); relation candidate(x:S); relation blocked(x:S);",
            "allowed(X) :- candidate(X), !blocked(X); blocked(X) :- candidate(X), !allowed(X);",
            "cycle through negation",
        ),
    ] {
        let text = format!("sort S; {declarations} input i(x:S) within allowed; {rules}");
        let errors = match parse(&text) {
            Err(e) => e,
            Ok(_) => panic!("accepted {text}"),
        };
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains(reason), "{errors:?}");
        assert_eq!(
            errors[0].range.start,
            text.find("within allowed").unwrap() + 7
        );
    }
    assert!(parse("relation allowed(); relation r() within allowed;").is_err());
}

#[test]
fn api_validation_and_export_roundtrip_share_the_same_contract() {
    let mut c = Corpus::new();
    let s = c.declare_sort("S").unwrap();
    let a = c.declare_constant("a", s).unwrap();
    let input = c
        .declare_relation("i", RelationRole::Input, [Parameter::new("x", s)])
        .unwrap();
    let provider = c
        .declare_relation("allowed", RelationRole::Derived, [Parameter::new("v", s)])
        .unwrap();
    assert!(c.restrict_input(provider, input).is_err());
    c.restrict_input(input, provider).unwrap();
    let head = c.atom(provider, [Term::Constant(a)]).unwrap();
    c.add_rule(head, []).unwrap();
    c.validate_input_domains().unwrap();
    let sources = Sources::new();
    let provenance = Provenance::new();
    let domains = Domains::from([(s, vec![a])]);
    let layout = ExportLayout {
        files: vec![ExportFile {
            path: "program.den".into(),
            ownership: Ownership::User,
        }],
        placements: top_level(&c).into_iter().map(|id| (id, 0)).collect(),
    };
    let export = ExportProgram {
        corpus: &c,
        domains: &domains,
        sources: &sources,
        provenance: &provenance,
        layout: &layout,
    };
    let bundle = print(&export, PrintOptions::default()).unwrap();
    assert!(bundle.files["program.den"].contains("within allowed"));
    let (membership, files) = bundle.documents("file:///roundtrip");
    let loaded = load(&membership, &files).unwrap();
    support::compare(&export, &loaded, "file:///roundtrip", false);
    assert_eq!(
        GroundProgram::prepare(&loaded.corpus, &loaded.domains, &Limits::default())
            .unwrap()
            .input_atoms()
            .count(),
        1
    );
    // A provider attached before rules must still be checked against the final graph.
    let head = c.atom(provider, [Term::Constant(a)]).unwrap();
    let body = c.atom(input, [Term::Constant(a)]).unwrap();
    c.add_rule(head, [Literal::Positive(body)]).unwrap();
    assert!(matches!(
        c.validate_input_domains(),
        Err(ConstructionError::InvalidInputDomain { .. })
    ));
    assert!(matches!(
        GroundProgram::prepare(&c, &domains, &Limits::default()),
        Err(CheckError::Construction(
            ConstructionError::InvalidInputDomain { .. }
        ))
    ));
}

#[test]
fn edited_provider_contents_and_sort_scope_refresh_warm_sessions() {
    let mut session = Session::default();
    for (facts, domain, count) in [
        ("", "", 0),
        ("allowed(a);", "", 1),
        ("allowed(a); allowed(b);", "", 2),
        ("allowed(b);", "", 1),
        ("", "", 0),
        ("allowed(a);", "domain S=[a];", 1),
    ] {
        let p = parse(&format!("{BASE}{facts}{domain}{CHECKS}")).unwrap();
        let warm = run(&p, &mut session);
        assert_eq!(warm.1.len(), count);
        assert_eq!(warm, run(&p, &mut Session::default()));
        let request = p
            .verification_requests(&Limits::default())
            .unwrap()
            .remove(0)
            .1;
        let ops = OperationalLimits::from(&Limits::default());
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        assert_eq!(prepared.program().input_atoms().count(), count);
        let prepared = prepared.admit(&ops).unwrap();
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!()
        };
        assert_eq!(report.verification.all_obligations_proved(), false); // coverage always has an all-absent counterexample
    }
}

#[test]
fn domain_limit_is_inconclusive_and_never_installs_a_partial_universe() {
    let p = parse(&format!("{BASE} allowed(a); allowed(b); {CHECKS}")).unwrap();
    let limits = Limits {
        max_atoms: 1,
        ..Limits::default()
    };
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let ops = OperationalLimits::from(&limits);
    let mut session = Session::default();
    for cached in [false, true] {
        let result = if cached {
            session.prepare(&request, &p.corpus, &p.keys, &ops)
        } else {
            request.prepare(&p.corpus, &p.keys, &ops)
        }
        .unwrap();
        let RequestPreparation::Inconclusive { reason, .. } = result else {
            panic!("partial domain accepted")
        };
        assert_eq!(reason.phase, "input domains");
        assert_eq!(reason.resource, "atoms");
    }
    let recovered = run(&p, &mut session);
    assert_eq!(recovered.1.len(), 2);
    assert_eq!(recovered, run(&p, &mut Session::default()));
}

#[test]
fn independent_small_world_oracle_matches_all_masks_and_both_preparation_paths() {
    for mask in 0..4 {
        let facts = format!(
            "{} {}",
            if mask & 1 != 0 { "allowed(a);" } else { "" },
            if mask & 2 != 0 { "allowed(b);" } else { "" }
        );
        for formula in 0..4 {
            let rule = [
                "bad() :- i(a), i(b);",
                "bad() :- i(a), !i(b);",
                "bad() :- !i(a), !i(b);",
                "bad() :- i(b);",
            ][formula];
            let p = parse(&format!("{BASE} {facts} relation bad(); {rule} obligation vacant: empty(bad); verification checks {{ assumptions:[]; obligations:[vacant]; }}")).unwrap();
            let ground = GroundProgram::prepare(&p.corpus, &p.domains, &Limits::default()).unwrap();
            let truth = |world: usize| match formula {
                0 => world == 3,
                1 => world == 1,
                2 => world == 0,
                _ => world & 2 != 0,
            };
            let mut possible = false;
            for world in (0..4).filter(|w| w & !mask == 0) {
                let present = ["a", "b"]
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| world & (1 << i) != 0)
                    .map(|(_, n)| atom(&p, "i", &[n]))
                    .collect::<Vec<_>>();
                let replay = ground
                    .evaluate(present.clone(), &Limits::default())
                    .unwrap();
                assert_eq!(
                    replay.fact(&atom(&p, "bad", &[])).unwrap(),
                    FactState::Settled(truth(world))
                );
                let CertificationOutcome::Certified(certified) = ground
                    .certify_observation(present, &Limits::default())
                    .unwrap()
                else {
                    panic!()
                };
                assert_eq!(
                    certified.facts.contains(&atom(&p, "bad", &[])),
                    truth(world)
                );
                assert_eq!(
                    certified.observation.present.len() + certified.observation.absent.len(),
                    mask.count_ones() as usize
                );
                possible |= truth(world);
            }
            for n in ["a", "b"]
                .into_iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) == 0)
                .map(|(_, n)| n)
            {
                assert!(matches!(
                    ground.certify_observation([atom(&p, "i", &[n])], &Limits::default()),
                    Err(CheckError::InvalidObservation(_))
                ));
            }
            let mut session = Session::default();
            let (cold, _) = run(&p, &mut session);
            assert_eq!(cold, run(&p, &mut session).0);
            assert_eq!(cold.emptiness.values().next().unwrap().proved(), !possible);
            let ops = OperationalLimits::from(&Limits::default());
            let request = p
                .verification_requests(&Limits::default())
                .unwrap()
                .remove(0)
                .1;
            let RequestPreparation::Complete(prepared) =
                request.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
                panic!()
            };
            assert_eq!(report.verification.all_obligations_proved(), !possible);
        }
    }
}

#[test]
fn library_provider_is_evaluated_in_each_consumer_and_is_independent_of_assumptions() {
    let library = SourceFile::new(
        "file:///lib/code.den",
        1,
        format!("namespace lib; {BASE} assumption single: at_most_one(i, group_by:()); {CHECKS}"),
    );
    let consumer_a = SourceFile::new("file:///a/code.den", 1, "lib::allowed(lib::a);");
    let consumer_b = SourceFile::new(
        "file:///b/code.den",
        1,
        "lib::allowed(lib::a); lib::allowed(lib::b); verification constrained { assumptions:[lib::single]; obligations:[lib::vacant]; }",
    );
    let roots = std::collections::BTreeMap::from([
        (
            "lib".into(),
            RootInfo {
                files: BTreeSet::from([library.uri.clone()]),
                libraries: BTreeSet::new(),
            },
        ),
        (
            "a".into(),
            RootInfo {
                files: BTreeSet::from([consumer_a.uri.clone()]),
                libraries: BTreeSet::from(["lib".into()]),
            },
        ),
        (
            "b".into(),
            RootInfo {
                files: BTreeSet::from([consumer_b.uri.clone()]),
                libraries: BTreeSet::from(["lib".into()]),
            },
        ),
    ]);
    let mut session = Session::default();
    for (root, count) in [("lib", 0), ("a", 1), ("b", 2), ("a", 1), ("lib", 0)] {
        let p = load(
            &ProgramMembership {
                root: root.into(),
                roots: roots.clone(),
            },
            &[library.clone(), consumer_a.clone(), consumer_b.clone()],
        )
        .unwrap();
        for (_, request) in p.verification_requests(&Limits::default()).unwrap() {
            let ops = OperationalLimits::from(&Limits::default());
            let RequestPreparation::Complete(prepared) =
                session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            assert_eq!(prepared.program().input_atoms().count(), count);
            let RequestPreparation::Complete(cold) =
                request.prepare(&p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!()
            };
            assert_eq!(
                prepared.program().input_atoms().collect::<Vec<_>>(),
                cold.program().input_atoms().collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn binary_domains_preserve_tuple_correlation_and_switching_restrictions_refreshes_sessions() {
    let body = "sort S; sort T; const a,b:S; const x,y:T;
        relation eligible(left:S,right:T); eligible(a,x); eligible(b,y);
        relation alternative(left:S,right:T); alternative(a,y);
        input i(left:S,right:T) DOMAIN;
        relation bad(); bad() :- i(a,y);
        obligation vacant: empty(bad); verification checks { assumptions:[]; obligations:[vacant]; }";
    let mut session = Session::default();
    for (restriction, count, proved) in [
        ("within eligible", 2, true),
        ("", 4, false),
        ("within alternative", 1, false),
        ("within eligible", 2, true),
    ] {
        let p = parse(&body.replace("DOMAIN", restriction)).unwrap();
        let warm = run(&p, &mut session);
        assert_eq!(warm.1.len(), count);
        assert_eq!(warm.0.emptiness.values().next().unwrap().proved(), proved);
        assert_eq!(warm, run(&p, &mut Session::default()));
        if proved {
            assert_eq!(
                warm.1,
                BTreeSet::from([
                    AtomKey::from_atom(&p.keys, &atom(&p, "i", &["a", "x"])).unwrap(),
                    AtomKey::from_atom(&p.keys, &atom(&p, "i", &["b", "y"])).unwrap(),
                ])
            );
        }
    }
}
