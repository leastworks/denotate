use super::*;
use denotate_ir::AssumptionCone;

fn prepared_for<'a>(p: &'a LoadedProgram, name: &str) -> PreparedCheck<'a> {
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p
        .verification_requests(&limits)
        .unwrap()
        .into_iter()
        .find(|(k, _)| k.0.name.as_ref() == name)
        .unwrap()
        .1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!("preparation exhausted")
    };
    prepared.admit(&ops).unwrap()
}

fn exercise(name: &str) -> Snapshot {
    let (membership, sources) =
        filesystem::discover(&root().join("10-computed-values/exercises").join(name)).unwrap();
    Snapshot {
        membership,
        sources,
    }
}

#[test]
fn step_10_computations_have_ground_meaning_and_varying_conditions() {
    let (code, reports) = cli(10);
    assert_eq!(code, 0);
    assert_eq!(reports.len(), 2);
    for report in reports.values() {
        assert_eq!(report["state"], "proved");
        assert_eq!(report["findings"], json!([]));
    }
    let notices = reports["shipping_example::valid_shipments"]["notices"]
        .as_array()
        .unwrap();
    assert_eq!(notices.len(), 3);
    assert!(notices.iter().all(|n| n["result"]["state"] == "varying"));

    let p = Snapshot::new(10).load();
    let assumption = p
        .corpus
        .assumptions()
        .find(|a| a.name == "valid_message")
        .unwrap();
    assert_eq!(
        p.corpus.validate_assumptions().unwrap()[&assumption.restriction.relation()],
        AssumptionCone::NeedsGrounding
    );
    assert!(
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &Limits::default())
            .unwrap()
            .is_valid()
    );
    let prepared = prepared_for(&p, "valid_shipments");
    assert!(prepared.program().components().all(|c| c.cycle.is_none()));
}

#[test]
fn computed_availability_matches_all_small_input_worlds() {
    let p = Snapshot::new(10).load();
    let input = |step, element, value| atom(&p, "shipping::step_result", &[step, element, value]);
    let domestic = input(
        "tasks::compute_zone",
        "shipment::zone",
        "literals::domestic",
    );
    let international = input(
        "tasks::compute_zone",
        "shipment::zone",
        "literals::international",
    );
    let reference = input(
        "tasks::prepare_customs",
        "shipment::customs_reference",
        "literals::reference",
    );
    let receipt = input(
        "tasks::prepare_customs",
        "shipment::receipt",
        "literals::receipt",
    );
    let emitted = atom(
        &p,
        "shipping::output_emitted",
        &["tasks::prepare_customs", "shipment::receipt"],
    );
    let details = atom(&p, "shipping_example::customs_details_received", &[]);
    let inputs = [
        domestic.clone(),
        international.clone(),
        reference.clone(),
        receipt.clone(),
        emitted.clone(),
        details.clone(),
    ];
    for (verification, expected_worlds) in [("computation_sources", 8), ("valid_shipments", 6)] {
        let prepared = prepared_for(&p, verification);
        let program = prepared.program();
        assert_eq!(
            program.input_atoms().cloned().collect::<BTreeSet<_>>(),
            inputs.iter().cloned().collect()
        );
        let mut permitted = 0;
        for bits in 0..(1 << inputs.len()) {
            let world = inputs
                .iter()
                .enumerate()
                .filter(|(i, _)| bits & (1 << i) != 0)
                .map(|(_, a)| a.clone())
                .collect::<BTreeSet<_>>();
            let is_domestic = world.contains(&domestic);
            let is_international = world.contains(&international);
            let valid = (is_domestic != is_international)
                && world.contains(&reference)
                && world.contains(&receipt)
                && (verification != "valid_shipments" || is_domestic || world.contains(&details));
            let replay = program.evaluate(world.iter().cloned(), &Limits::default());
            if !valid {
                assert!(
                    matches!(replay, Err(CheckError::InvalidInputGroup(_))),
                    "{verification}: {bits}"
                );
                continue;
            }
            permitted += 1;
            let replay = replay.unwrap();
            assert!(replay.is_complete());
            for (fact, expected) in [
                (
                    atom(&p, "shipping::step_applies", &["tasks::compute_zone"]),
                    true,
                ),
                (
                    atom(&p, "shipping::element_present", &["shipment::zone"]),
                    true,
                ),
                (
                    atom(&p, "shipping::classified", &["term_ids::domestic"]),
                    is_domestic,
                ),
                (
                    atom(&p, "shipping::step_applies", &["tasks::prepare_customs"]),
                    is_international,
                ),
                (
                    atom(
                        &p,
                        "shipping::element_value",
                        &["shipment::customs_reference", "literals::reference"],
                    ),
                    is_international,
                ),
                (
                    atom(&p, "shipping::element_present", &["shipment::receipt"]),
                    is_international && world.contains(&emitted),
                ),
                (
                    atom(
                        &p,
                        "shipping::writes",
                        &["tasks::prepare_customs", "shipment::receipt"],
                    ),
                    is_international && world.contains(&emitted),
                ),
            ] {
                assert_eq!(
                    replay.fact(&fact).unwrap(),
                    FactState::Settled(expected),
                    "{verification}: {bits}"
                );
            }
        }
        assert_eq!(permitted, expected_worlds);
    }
}

#[test]
fn conditional_required_output_breaks_the_contract_and_repairs_cold_and_warm() {
    let mut s = Snapshot::new(10);
    let mut session = Session::with_grounding();
    for conditional in [false, true, false] {
        if conditional {
            s.replace(
                "program.den",
                "required_output(prepare_customs, shipment::customs_reference);",
                "conditional_output(prepare_customs, shipment::customs_reference);",
            );
        } else if s.sources.iter().any(|s| {
            s.text
                .contains("conditional_output(prepare_customs, shipment::customs_reference);")
        }) {
            s.replace(
                "program.den",
                "conditional_output(prepare_customs, shipment::customs_reference);",
                "required_output(prepare_customs, shipment::customs_reference);",
            );
        }
        let p = s.load();
        let warm = check(&p, &mut session);
        let cold = check(&p, &mut Session::default());
        assert_eq!(outcomes(&warm), outcomes(&cold));
        let result = &warm["shipping_example::valid_shipments"];
        assert_eq!(
            result.summary["state"],
            if conditional { "findings" } else { "proved" }
        );
        if conditional {
            assert!(
                result.summary["findings"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|f| f["kind"] == "counterexample"
                        && f["identity"]["obligation"]
                            == json!(["shipping_example", "no_missing_customs_reference"]))
            );
        }
    }
}

#[test]
fn sparse_output_coverage_does_not_hide_an_output_with_no_candidates() {
    let mut s = Snapshot::new(10);
    s.replace(
        "program.den",
        "result_choice(prepare_customs, shipment::customs_reference, literals::reference);",
        "",
    );
    let p = s.load();
    let results = check(&p, &mut Session::default());
    assert!(
        results
            .values()
            .all(|r| r.summary["state"] == "inconsistent-assumptions")
    );
}

#[test]
fn a_positive_task_loop_cannot_start_itself_and_an_explicit_seed_repairs_it() {
    let mut s = exercise("self-support");
    let (code, reports) = cli_at(root().join("10-computed-values/exercises/self-support"));
    assert_eq!(code, 0);
    assert_eq!(
        reports["loop::inspect"]["notices"][0]["result"]["state"],
        "impossible"
    );
    let p = s.load();
    let prepared = prepared_for(&p, "inspect");
    let replay = prepared
        .program()
        .evaluate(
            prepared.program().input_atoms().cloned(),
            &Limits::default(),
        )
        .unwrap();
    assert_eq!(
        replay
            .fact(&atom(&p, "shipping::step_applies", &["loop::assess"]))
            .unwrap(),
        FactState::Settled(false)
    );
    assert_eq!(
        replay
            .fact(&atom(&p, "shipping::element_present", &["loop::zone"]))
            .unwrap(),
        FactState::Settled(false)
    );
    let mut session = Session::with_grounding();
    check(&p, &mut session);
    s.replace(
        "program.den",
        "step_applies(assess) :- $ready();",
        "step_applies(assess);",
    );
    let fixed = s.load();
    let warm = check(&fixed, &mut session);
    assert_eq!(
        outcomes(&warm),
        outcomes(&check(&fixed, &mut Session::default()))
    );
    assert_eq!(
        warm["loop::inspect"].summary["notices"][0]["result"]["state"],
        "always-true"
    );
}

#[test]
fn negative_task_loop_has_no_meaning_and_cannot_become_a_validity_assumption() {
    let mut s = exercise("negative-cycle");
    let (code, reports) = cli_at(root().join("10-computed-values/exercises/negative-cycle"));
    assert_eq!(code, 1);
    assert!(
        reports["loop::inspect"]["findings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["kind"] == "no-meaning")
    );
    assert_eq!(
        reports["loop::inspect"]["notices"][0]["result"]["state"],
        "unknown"
    );
    s.append("namespace loop; relation invalid_message(); invalid_message() :- !shipping::classified(ready); assumption valid_message: empty(invalid_message);");
    let p = s.load();
    let validation =
        validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &Limits::default()).unwrap();
    assert!(
        validation
            .assumptions
            .iter()
            .any(|(k, state)| k.0.name.as_ref() == "valid_message"
                && matches!(state, AssumptionValidity::Invalid { .. }))
    );
    let diagnostics = presentation::present_assumption_validation(&p, &validation).unwrap();
    assert!(
        diagnostics
            .diagnostics
            .iter()
            .any(|d| d.kind.code() == "invalid-assumption")
    );
    s.replace(
        "program.den",
        "step_applies(assess) :- $not_ready();",
        "step_applies(assess);",
    );
    let repaired = s.load();
    assert!(
        validate_assumption_cones(
            &repaired.corpus,
            &repaired.domains,
            &repaired.keys,
            &Limits::default()
        )
        .unwrap()
        .is_valid()
    );
    let results = check(&repaired, &mut Session::default());
    assert!(results.values().all(|r| r.summary["state"] == "proved"));
    assert_eq!(
        results["loop::inspect"].summary["notices"][0]["result"]["state"],
        "impossible"
    );
}
