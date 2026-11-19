use super::*;

const CASES: [&str; 12] = [
    "w1-self-reading-set",
    "w2-self-reading-computation",
    "w3-self-negating-set",
    "w4-self-negating-computation",
    "k1-exhaustive-guards",
    "k1u-without-lift",
    "k1s-swapped-validation",
    "k2-self-reading-expectation",
    "k3-self-negating-expectation",
    "k3b-conditional-expectation",
    "k4-partial-classification",
    "k5-every-leaf-supplies",
];
fn snapshot(case: usize) -> Snapshot {
    let (membership, sources) =
        filesystem::discover(&root().join(STEPS[10]).join("cases").join(CASES[case])).unwrap();
    Snapshot {
        membership,
        sources,
    }
}
fn inputs(case: usize) -> Vec<(&'static str, &'static str)> {
    match case {
        0..=3 => vec![("g", "one"), ("g", "two")],
        4..=8 => vec![("fee", "zero"), ("fee", "five")],
        9 => vec![("fee", "zero"), ("fee", "five"), ("g", "one"), ("g", "two")],
        _ => vec![("kind", "r"), ("kind", "s"), ("f", "ten"), ("f", "twenty")],
    }
}
fn computed(case: usize) -> bool {
    matches!(case, 1 | 3)
}
fn has_unknown(case: usize) -> bool {
    matches!(case, 0..=3 | 5 | 7..=9)
}

// Per-message semantics, written directly over the source statements. This does
// not read gate facts, the .den graph or any checker result. Tests additionally
// assert the brief's world table independently of this fixed-point comparison.
fn case_reference(case: usize, raw: &[bool]) -> BTreeMap<&'static str, Truth> {
    let mut state = BTreeMap::new();
    for _ in 0..100 {
        let get = |name: &str| state.get(name).copied().unwrap_or(Unknown);
        let mut next = BTreeMap::new();
        if case <= 3 {
            let g_one = Truth::from_bool(raw[0]); // g is unconditionally owned.
            let a = if computed(case) {
                get("writer").read(true) // required single-valued output
            } else {
                get("writer")
            };
            let guard = if case >= 2 { a.not() } else { a };
            next.extend([
                ("path", True),
                ("accept_g", True),
                ("raw_g_one", g_one),
                ("g_one", g_one),
                ("a_present", a),
                ("a_absent", a.not()),
                ("writer", guard.and(g_one)),
                ("recognized", True),
            ]);
            if computed(case) {
                next.insert("raw_result", True);
            }
        } else if case <= 9 {
            let accepted = get("accept_fee");
            let zero = accepted.read(raw[0]);
            let present = accepted.read(raw[0] || raw[1]);
            let g = if case == 9 {
                Truth::from_bool(raw[2])
            } else {
                True
            };
            let gives = match case {
                4..=6 => zero.not().or(zero),
                7 => present,
                8 => present.not(),
                9 => present.not().and(g),
                _ => unreachable!(),
            };
            let acceptance = if matches!(case, 4 | 6) { True } else { gives };
            let required = match case {
                4 | 5 => zero.not(),
                6 => zero,
                _ => gives,
            };
            // A matched leaf validates its original declarations, even when
            // ownership was lifted. Validation never determines that path.
            let missing = required.and(present.not());
            next.extend([
                ("path", True),
                ("yes", True),
                ("accept_fee", acceptance),
                ("raw_zero", Truth::from_bool(raw[0])),
                ("raw_five", Truth::from_bool(raw[1])),
                ("raw_present", Truth::from_bool(raw[0] || raw[1])),
                ("fee_zero", zero),
                ("fee_nonzero", zero.not()),
                ("fee_present", present),
                ("fee_absent", present.not()),
                ("gives_fee", gives),
                ("required_guard", required),
                ("missing", missing),
                ("valid", missing.not()),
                ("recognized", missing.not()),
            ]);
            if case == 9 {
                next.extend([("accept_g", True), ("raw_g_one", g), ("g_one", g)]);
            }
        } else {
            // A = kind r. B = kind s AND f ten. B always supplies f;
            // k4 A does not, k5 A does. Excluding A can unlock f before B matches.
            let a = Truth::from_bool(raw[0]);
            let s = Truth::from_bool(raw[1]);
            let acceptance = if case == 11 { True } else { a.not() };
            let f_ten = get("accept_f").read(raw[2]);
            let present = get("accept_f").read(raw[2] || raw[3]);
            let kind_present = Truth::from_bool(raw[0] || raw[1]);
            let b = s.and(f_ten);
            let missing_a_kind = a.and(kind_present.not());
            let missing_b_kind = b.and(kind_present.not());
            let missing_f = b.and(present.not());
            let missing_kind = missing_a_kind.or(missing_b_kind);
            let invalid = missing_kind.or(missing_f);
            next.extend([
                ("yes", True),
                ("accept_kind", True),
                ("accept_f", acceptance),
                ("raw_r", a),
                ("raw_s", s),
                ("raw_ten", Truth::from_bool(raw[2])),
                ("raw_twenty", Truth::from_bool(raw[3])),
                ("raw_kind_present", kind_present),
                ("raw_f_present", Truth::from_bool(raw[2] || raw[3])),
                ("kind_r", a),
                ("kind_s", s),
                ("kind_present", kind_present),
                ("f_ten", f_ten),
                ("f_present", present),
                ("a", a),
                ("b", b),
                ("path", a.or(b)),
                ("missing_a_kind", missing_a_kind),
                ("missing_b_kind", missing_b_kind),
                ("missing_f", missing_f),
                ("missing_kind", missing_kind),
                ("invalid", invalid),
                ("valid", invalid.not()),
                ("recognized", a.or(b).and(invalid.not())),
            ]);
        }
        if state == next {
            return state;
        }
        assert!(
            state
                .iter()
                .all(|(k, v)| *v == Unknown || next.get(k) == Some(v))
        );
        state = next;
    }
    panic!("reference failed to converge: {}", CASES[case]);
}

fn assert_world_table(case: usize, raw: &[bool], values: &BTreeMap<&str, Truth>) {
    match case {
        0..=3 => {
            assert_eq!(values["writer"], if raw[0] { Unknown } else { False });
            assert_eq!(values["a_present"], if raw[0] { Unknown } else { False });
        }
        4 | 6 => {
            assert_eq!(values["accept_fee"], True);
            assert_eq!(
                values["missing"],
                Truth::from_bool(case == 4 && !raw[0] && !raw[1])
            );
            assert_eq!(values["recognized"], values["missing"].not());
        }
        5 | 7 | 8 => {
            for name in ["accept_fee", "fee_present", "missing", "recognized"] {
                assert_eq!(values[name], Unknown, "{name}");
            }
        }
        9 => {
            assert_eq!(values["accept_fee"], if raw[2] { Unknown } else { False });
            assert_eq!(values["recognized"], if raw[2] { Unknown } else { True });
        }
        _ => {
            assert_eq!(values["accept_f"], Truth::from_bool(case == 11 || !raw[0]));
            assert_eq!(
                values["recognized"],
                Truth::from_bool(raw[0] || (raw[1] && raw[2]))
            );
            // With kind s and f absent/20, B fails classification. It never
            // matches, so this must not become a required-field failure.
            assert_eq!(values["missing_f"], False);
        }
    }
}

#[test]
fn ten_programs_and_controls_match_the_reference_in_every_world() {
    let mut permitted_count = 0;
    let mut assignments = 0;
    for case in 0..CASES.len() {
        let p = snapshot(case).load();
        let limits = Limits::default();
        let prep = prepared(&p, "propagation", &limits);
        let pairs = inputs(case);
        let mut atoms = pairs
            .iter()
            .map(|(f, v)| {
                atom(
                    &p,
                    "schema::raw_value",
                    &[&format!("fields::{f}"), &format!("values::{v}")],
                )
            })
            .collect::<Vec<_>>();
        if computed(case) {
            atoms.push(atom(
                &p,
                "schema::computed_result",
                &["statements::writer", "fields::a", "values::one"],
            ));
        }
        assert_eq!(
            prep.program()
                .input_atoms()
                .cloned()
                .collect::<BTreeSet<_>>(),
            atoms.iter().cloned().collect()
        );
        for bits in 0..1 << atoms.len() {
            assignments += 1;
            let raw = (0..atoms.len())
                .map(|i| bits & (1 << i) != 0)
                .collect::<Vec<_>>();
            let world = atoms
                .iter()
                .zip(&raw)
                .filter(|(_, yes)| **yes)
                .map(|(a, _)| a.clone())
                .collect::<Vec<_>>();
            let replay = prep.program().evaluate(world, &limits);
            let scalar = raw[..pairs.len()].chunks(2).all(|p| !(p[0] && p[1]));
            let complete_result = !computed(case) || raw[pairs.len()];
            if !scalar || !complete_result {
                assert!(
                    matches!(
                        replay,
                        Err(CheckError::InvalidObservation(_) | CheckError::InvalidInputGroup(_))
                    ),
                    "{} {bits}: {replay:?}",
                    CASES[case]
                );
                continue;
            }
            permitted_count += 1;
            let replay = replay.unwrap();
            assert!(replay.is_complete());
            let expected = case_reference(case, &raw);
            assert_world_table(case, &raw, &expected);
            for (name, truth) in expected {
                for (positive, value) in [(true, truth == True), (false, truth == False)] {
                    assert_eq!(
                        replay.fact(&decision(&p, name, positive)).unwrap(),
                        FactState::Settled(value),
                        "{} world {bits}, {name}, positive={positive}",
                        CASES[case]
                    );
                }
            }
        }
    }
    assert_eq!((assignments, permitted_count), (92, 54));
}

#[test]
fn loop_cases_report_unknowns_without_filtering_them_and_agree_cold_warm() {
    for case in 0..CASES.len() {
        let s = snapshot(case);
        let p = s.load();
        let mut session = Session::with_grounding();
        let cold = check(&p, &mut session);
        let warm = check(&p, &mut session);
        let fresh = check(&p, &mut Session::default());
        assert_eq!(outcomes(&cold), outcomes(&warm));
        assert_eq!(outcomes(&warm), outcomes(&fresh));
        let result = &warm["schema::propagation"];
        assert_eq!(
            failed(result),
            if has_unknown(case) {
                BTreeSet::from(["no_unknown_decisions".into()])
            } else {
                BTreeSet::new()
            },
            "{}",
            CASES[case]
        );
        let (exit, reports) = cli_at(root().join(STEPS[10]).join("cases").join(CASES[case]));
        assert_eq!(exit, u8::from(has_unknown(case)), "{}", CASES[case]);
        assert_eq!(
            reports["schema::propagation"]["state"],
            result.summary["state"]
        );
    }
}

#[test]
fn repairing_a_self_reading_expectation_agrees_after_warm_edits() {
    let mut s = snapshot(9);
    let original = "both(decisions::gives_fee, decisions::fee_absent, decisions::g_one);";
    let repaired = "same(decisions::gives_fee, decisions::g_one);";
    let mut session = Session::with_grounding();
    for broken in [true, false, true] {
        if !broken {
            s.replace("program.den", original, repaired);
        } else if s.sources.iter().any(|s| s.text.contains(repaired)) {
            s.replace("program.den", repaired, original);
        }
        let p = s.load();
        let warm = check(&p, &mut session);
        assert_eq!(
            outcomes(&warm),
            outcomes(&check(&p, &mut Session::default()))
        );
        assert_eq!(
            failed(&warm["schema::propagation"]).contains("no_unknown_decisions"),
            broken
        );
        if !broken {
            // g=1, no fee: the repaired declaration now produces a known
            // missing-value rejection, not a stuck acceptance decision.
            let prep = prepared(&p, "propagation", &Limits::default());
            let replay = prep
                .program()
                .evaluate(
                    [atom(&p, "schema::raw_value", &["fields::g", "values::one"])],
                    &Limits::default(),
                )
                .unwrap();
            assert_eq!(
                replay.fact(&decision(&p, "missing", true)).unwrap(),
                FactState::Settled(true)
            );
            assert_eq!(
                replay.fact(&decision(&p, "recognized", false)).unwrap(),
                FactState::Settled(true)
            );
        }
    }
}

#[test]
fn declared_absent_validation_rejects_present_values_without_changing_the_path() {
    let mut s = snapshot(6); // accepted field; original guard is fee = 0
    s.replace(
        "program.den",
        "required_field(decisions::missing",
        "absent_field(decisions::missing",
    );
    let p = s.load();
    let prep = prepared(&p, "propagation", &Limits::default());
    for value in [None, Some("zero"), Some("five")] {
        let world = value.map(|v| {
            atom(
                &p,
                "schema::raw_value",
                &["fields::fee", &format!("values::{v}")],
            )
        });
        let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
        assert_eq!(
            replay.fact(&decision(&p, "path", true)).unwrap(),
            FactState::Settled(true)
        );
        assert_eq!(
            replay.fact(&decision(&p, "recognized", true)).unwrap(),
            FactState::Settled(value != Some("zero"))
        );
        assert_eq!(
            replay
                .fact(&atom(
                    &p,
                    "schema::forbidden_field",
                    &["formats::request", "fields::fee"]
                ))
                .unwrap(),
            FactState::Settled(value == Some("zero"))
        );
    }
}

#[test]
fn an_independent_guard_is_not_erased_by_exhaustive_field_guards() {
    let mut s = snapshot(9);
    s.replace(
        "program.den",
        "both(decisions::gives_fee, decisions::fee_absent, decisions::g_one);",
        "namespace decisions { const exhaustive_fee: Decision; } either(decisions::exhaustive_fee, decisions::fee_zero, decisions::fee_nonzero); both(decisions::gives_fee, decisions::g_one, decisions::exhaustive_fee);",
    );
    let p = s.load();
    let prep = prepared(&p, "propagation", &Limits::default());
    for g in [None, Some("one"), Some("two")] {
        for fee in [None, Some("zero"), Some("five")] {
            let world = [("g", g), ("fee", fee)].into_iter().filter_map(|(f, v)| {
                v.map(|v| {
                    atom(
                        &p,
                        "schema::raw_value",
                        &[&format!("fields::{f}"), &format!("values::{v}")],
                    )
                })
            });
            let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
            // G AND (fee=0 OR fee!=0) cannot become unconditional ownership.
            assert_eq!(
                replay.fact(&decision(&p, "accept_fee", true)).unwrap(),
                FactState::Settled(false)
            );
            assert_eq!(
                replay.fact(&decision(&p, "accept_fee", false)).unwrap(),
                FactState::Settled(g != Some("one"))
            );
        }
    }
}

#[test]
fn an_independent_start_unlocks_literal_and_computed_writers() {
    for case in [0, 1] {
        let mut s = snapshot(case);
        s.replace(
            "program.den",
            "both(decisions::writer, decisions::a_present, decisions::g_one);",
            "same(decisions::writer, decisions::g_one);",
        );
        let p = s.load();
        let prep = prepared(&p, "propagation", &Limits::default());
        for g in [None, Some("one"), Some("two")] {
            let mut world = g
                .map(|v| {
                    atom(
                        &p,
                        "schema::raw_value",
                        &["fields::g", &format!("values::{v}")],
                    )
                })
                .into_iter()
                .collect::<Vec<_>>();
            if computed(case) {
                world.push(atom(
                    &p,
                    "schema::computed_result",
                    &["statements::writer", "fields::a", "values::one"],
                ));
            }
            let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
            let active = g == Some("one");
            assert_eq!(
                replay.fact(&decision(&p, "a_present", true)).unwrap(),
                FactState::Settled(active)
            );
            assert_eq!(
                replay.fact(&decision(&p, "a_present", false)).unwrap(),
                FactState::Settled(!active)
            );
            let relation = if computed(case) {
                "schema::computed_value"
            } else {
                "schema::set_value"
            };
            assert_eq!(
                replay
                    .fact(&atom(&p, relation, &["fields::a", "values::one"]))
                    .unwrap(),
                FactState::Settled(active)
            );
        }
        assert!(failed(&check(&p, &mut Session::default())["schema::propagation"]).is_empty());
    }
}

#[test]
fn missing_computation_candidates_are_structural_findings_and_repair_cold_warm() {
    let mut s = snapshot(1); // W2: self-reading computation.
    let mut session = Session::with_grounding();
    let fact = "result_choice(statements::writer, fields::a, values::one);";
    for missing in [false, true, false] {
        if missing {
            s.replace("program.den", fact, "// removed result candidate");
        } else if s
            .sources
            .iter()
            .any(|source| source.text.contains("// removed result candidate"))
        {
            s.replace("program.den", "// removed result candidate", fact);
        }
        let p = s.load();
        let warm = check(&p, &mut session);
        assert_eq!(
            outcomes(&warm),
            outcomes(&check(&p, &mut Session::default()))
        );
        let findings = warm["schema::propagation"].summary["findings"]
            .as_array()
            .unwrap();
        assert_eq!(
            findings.iter().any(|f| f["kind"] == "counterexample"
                && f["identity"]["obligation"]
                    == json!(["schema", "no_missing_result_candidates"])),
            missing
        );
    }
}
