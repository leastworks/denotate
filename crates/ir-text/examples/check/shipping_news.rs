//! The public tutorial's runnable programs and exercises are the test inputs.
//! Use the actual CLI for documented outcomes, and its checker path for edits,
//! placement and input-world semantics. No witness or rendered-text goldens.
use super::run;
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::{Namespace, RelationId};
use denotate_ir_text::{
    LoadedProgram, ProgramMembership, SourceFile, filesystem, load, presentation,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

const STEPS: [&str; 9] = [
    "01-declarations",
    "02-direct-mappings",
    "03-guards",
    "04-converters",
    "05-toggles-and-flags",
    "06-check-contracts",
    "07-classifications",
    "08-condition-notices",
    "09-complete",
];
fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../editors/den/examples/shipping-news")
}
fn cli(step: usize) -> (u8, BTreeMap<String, Value>) {
    cli_at(root().join(STEPS[step - 1]))
}
fn cli_at(path: PathBuf) -> (u8, BTreeMap<String, Value>) {
    let mut output = String::new();
    let code = run([path.display().to_string(), "--json".into()], &mut output).unwrap();
    let reports = output
        .split("\nVerification ")
        .skip(1)
        .map(|block| {
            let name = block.lines().next().unwrap().to_owned();
            let (_, data) = block
                .split_once("Results: ")
                .expect("every step finishes checking");
            let value = serde_json::Deserializer::from_str(data)
                .into_iter::<Value>()
                .next()
                .unwrap()
                .unwrap();
            (name, value)
        })
        .collect();
    (code, reports)
}
fn kinds(reports: &BTreeMap<String, Value>) -> BTreeMap<String, Vec<String>> {
    reports
        .iter()
        .map(|(key, v)| {
            let mut kinds = v["findings"]
                .as_array()
                .unwrap()
                .iter()
                .map(|f| f["kind"].as_str().unwrap().to_owned())
                .collect::<Vec<_>>();
            kinds.sort();
            (key.clone(), kinds)
        })
        .collect()
}
fn baseline(step: usize) {
    let (code, reports) = cli(step);
    assert_eq!(code, if step <= 3 { 1 } else { 0 });
    let expected_verifications = match step {
        1 => 1,
        2 => 2,
        3..=5 => 4,
        6..=7 => 5,
        _ => 6,
    };
    assert_eq!(reports.len(), expected_verifications, "{reports:#?}");
    let failing = match step {
        1 => Some("shipping::declarations"),
        2 => Some("shipping::mapping_types"),
        3 => Some("shipping::mappings"),
        _ => None,
    };
    for (name, report) in &reports {
        assert_eq!(
            report["state"],
            if Some(name.as_str()) == failing {
                "findings"
            } else {
                "proved"
            },
            "{name}: {report:#?}"
        );
    }
    if let Some(failing) = failing {
        let finding = &reports[failing]["findings"][0];
        let (obligation, component) = match step {
            1 => ("typed_fields", "coverage"),
            2 => ("compatible_mappings", "emptiness"),
            _ => ("one_inbound_source", ""),
        };
        assert_eq!(
            if step == 3 {
                &finding["identity"]["group"]["obligation"]
            } else {
                &finding["identity"]["obligation"]
            },
            &json!(["shipping", obligation])
        );
        if !component.is_empty() {
            assert_eq!(finding["identity"]["component"], component);
        }
    }
    let found = kinds(&reports);
    for (name, kinds) in found {
        let expected = if Some(name.as_str()) == failing {
            vec!["counterexample"]
        } else if step >= 8 && name == "authoring::conditions" {
            vec!["always-true-condition", "impossible-condition"]
        } else {
            vec![]
        };
        assert_eq!(kinds, expected, "step {step}: {name}");
    }
    if step >= 8 {
        let states = reports["authoring::conditions"]["notices"]
            .as_array()
            .unwrap()
            .iter()
            .map(|n| {
                (
                    n["identity"]["notice"][1].as_str().unwrap().to_owned(),
                    n["result"]["state"].as_str().unwrap().to_owned(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            states,
            BTreeMap::from([
                ("outer".into(), "varying".into()),
                ("nested".into(), "varying".into()),
                ("repeated".into(), "always-true".into()),
                ("impossible".into(), "impossible".into()),
                ("suppressed".into(), "parent-unreachable".into())
            ])
        );
    }
}
macro_rules! step {
    ($name:ident,$n:expr) => {
        #[test]
        fn $name() {
            baseline($n)
        }
    };
}
step!(step_01_declarations, 1);
step!(step_02_direct_mappings, 2);
step!(step_03_guards, 3);
step!(step_04_converters, 4);
step!(step_05_toggles_and_flags, 5);
step!(step_06_check_contracts, 6);
step!(step_07_classifications, 7);
step!(step_08_condition_notices, 8);
step!(step_09_complete, 9);

struct Snapshot {
    membership: ProgramMembership,
    sources: Vec<SourceFile>,
}
impl Snapshot {
    fn new(step: usize) -> Self {
        let (membership, sources) = filesystem::discover(&root().join(STEPS[step - 1])).unwrap();
        Self {
            membership,
            sources,
        }
    }
    fn load(&self) -> LoadedProgram {
        load(&self.membership, &self.sources).unwrap()
    }
    fn replace(&mut self, file: &str, from: &str, to: &str) {
        let source = self
            .sources
            .iter_mut()
            .find(|s| {
                s.uri
                    == format!(
                        "{}/{file}",
                        self.membership.root.trim_end_matches("/den.root")
                    )
            })
            .unwrap();
        assert!(
            source.text.contains(from),
            "missing exercise target {file}: {from}"
        );
        source.text = source.text.replace(from, to).into();
        source.revision += 1;
    }
    fn append(&mut self, text: &str) {
        let uri = format!(
            "{}/probe.den",
            self.membership.root.trim_end_matches("/den.root")
        );
        self.membership
            .roots
            .get_mut(&self.membership.root)
            .unwrap()
            .files
            .insert(uri.clone());
        self.sources.push(SourceFile::new(uri, 1, text));
    }
    fn exercise(&mut self, name: &str) {
        self.append(
            &std::fs::read_to_string(root().join("exercises").join(format!("{name}.den.txt")))
                .unwrap(),
        );
    }
}
struct Checked {
    summary: Value,
    diagnostics: Vec<denotate_presentation::Diagnostic>,
}
fn check(p: &LoadedProgram, session: &mut Session) -> BTreeMap<String, Checked> {
    let limits = Limits::default();
    let ops = (&limits).into();
    p.verification_requests(&limits)
        .unwrap()
        .into_iter()
        .map(|(key, request)| {
            let RequestPreparation::Complete(prepared) =
                session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
            else {
                panic!("preparation exhausted")
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(result) = session.verify(&prepared, &ops).unwrap()
            else {
                panic!("checking exhausted")
            };
            let out = presentation::present(p, &result.checked).unwrap();
            (
                format!("{}::{}", key.0.namespace, key.0.name),
                Checked {
                    summary: out.status,
                    diagnostics: out.diagnostics,
                },
            )
        })
        .collect()
}
fn outcomes(r: &BTreeMap<String, Checked>) -> Value {
    json!(
        r.iter()
            .map(|(k, r)| {
                let findings = r.summary["findings"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|f| json!({"kind":f["kind"],"identity":f["identity"]}))
                    .collect::<Vec<_>>();
                let notices = r.summary["notices"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|n| json!({"identity":n["identity"],"state":n["result"]["state"]}))
                    .collect::<Vec<_>>();
                (
                    k,
                    json!({"state":r.summary["state"],"findings":findings,"notices":notices}),
                )
            })
            .collect::<BTreeMap<_, _>>()
    )
}
#[test]
fn documented_repairs_clear_findings_at_the_authored_locations() {
    for (step, verification, file, from, to, anchor) in [
        (
            1,
            "shipping::declarations",
            "declarations.den",
            "// Intentionally missing: field_type(destination, text);",
            "field_type(destination, text);",
            "destination",
        ),
        (
            2,
            "shipping::mapping_types",
            "mappings.den",
            "inbound_mapping(carrier::mass, shipment::country);",
            "",
            "inbound_mapping(carrier::mass, shipment::country)",
        ),
        (
            3,
            "shipping::mappings",
            "mappings.den",
            "!field_value(carrier::service, literals::standard)",
            "!field_value(carrier::service, literals::express)",
            "applicable_inbound_mapping",
        ),
    ] {
        let mut s = Snapshot::new(step);
        let p = s.load();
        let mut session = Session::default();
        let bad = check(&p, &mut session);
        assert_eq!(bad[verification].summary["state"], "findings");
        assert!(
            bad[verification]
                .diagnostics
                .iter()
                .any(|d| d.kind.code() == "counterexample"
                    && !d.fallback
                    && p.sources.text(d.primary).unwrap().contains(anchor))
        );
        s.replace(file, from, to);
        let fixed = s.load();
        let warm = check(&fixed, &mut session);
        let cold = check(&fixed, &mut Session::default());
        assert_eq!(outcomes(&warm), outcomes(&cold));
        assert_eq!(warm[verification].summary["state"], "proved");
    }
}
#[test]
fn final_sample_agrees_cold_warm_after_trivia_and_does_not_rely_on_private_sources() {
    let mut s = Snapshot::new(9);
    let mut cache = Session::default();
    let before = check(&s.load(), &mut cache);
    for source in &mut s.sources {
        source.text = format!("{}\n// fresh snapshot\n", source.text).into();
        source.revision += 1;
    }
    let p = s.load();
    let warm = check(&p, &mut cache);
    let cold = check(&p, &mut Session::default());
    assert_eq!(outcomes(&before), outcomes(&warm));
    assert_eq!(outcomes(&warm), outcomes(&cold));
    assert!(
        s.sources
            .iter()
            .all(|s| s.uri.contains("/shipping-news/09-complete/"))
    );
}
#[test]
fn exercises_expose_unselected_contract_circular_reasoning_and_inconsistency() {
    for (exercise, verification, state, kind) in [
        (
            "without-contract",
            "experiments::without_contract",
            "findings",
            "counterexample",
        ),
        (
            "assumed-conclusion",
            "experiments::circular_audit",
            "proved",
            "assumed-conclusion",
        ),
        (
            "inconsistent",
            "experiments::impossible_context",
            "inconsistent-assumptions",
            "inconsistent-assumptions",
        ),
    ] {
        let mut s = Snapshot::new(6);
        s.exercise(exercise);
        let p = s.load();
        let r = check(&p, &mut Session::default());
        assert_eq!(r[verification].summary["state"], state, "{exercise}");
        assert!(
            r[verification]
                .diagnostics
                .iter()
                .any(|d| d.kind.code() == kind),
            "{exercise}"
        );
        assert_eq!(r["shipping::mappings"].summary["state"], "proved");
        if exercise == "inconsistent" {
            assert_eq!(r[verification].summary["groups"], json!([]));
        }
    }
}
#[test]
fn named_recursive_boundary_is_unsupported_and_phase_correlation_is_not_proved() {
    for (step, exercise, verification, state, kind) in [
        (
            7,
            "named-boundary",
            "boundary::extracted_term",
            "incomplete",
            "unsupported-region",
        ),
        (
            9,
            "phase-gap",
            "experiments::phase_correlation",
            "findings",
            "counterexample",
        ),
    ] {
        let mut s = Snapshot::new(step);
        if exercise == "named-boundary" {
            let path = root().join("exercises/named-boundary");
            let (membership, sources) = filesystem::discover(&path).unwrap();
            s = Snapshot {
                membership,
                sources,
            };
            let (code, reports) = cli_at(path);
            assert_eq!(code, 2);
            assert_eq!(reports[verification]["state"], state);
        } else {
            s.exercise(exercise);
        }
        let p = s.load();
        let r = check(&p, &mut Session::default());
        assert_eq!(r[verification].summary["state"], state);
        assert!(
            r[verification]
                .diagnostics
                .iter()
                .any(|d| d.kind.code() == kind)
        );
    }
}
fn relation(p: &LoadedProgram, qualified: &str) -> RelationId {
    let (ns, name) = qualified.rsplit_once("::").unwrap();
    p.corpus
        .relations()
        .find(|r| {
            r.name == name
                && p.corpus.namespace(r.id) == Some(&Namespace::new(ns.split("::")).unwrap())
        })
        .unwrap()
        .id
}
fn atom(p: &LoadedProgram, rel: &str, args: &[&str]) -> GroundAtom {
    let args = args.iter().map(|qualified| {
        let (ns, name) = qualified.rsplit_once("::").unwrap();
        p.corpus
            .constants()
            .find(|c| {
                c.name == name
                    && p.corpus.namespace(c.id) == Some(&Namespace::new(ns.split("::")).unwrap())
            })
            .unwrap()
            .id
    });
    GroundAtom::new(relation(p, rel), args)
}
fn prepared<'a>(p: &'a LoadedProgram) -> PreparedCheck<'a> {
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p
        .verification_requests(&limits)
        .unwrap()
        .into_iter()
        .find(|(k, _)| k.0.name.as_ref() == "mappings")
        .unwrap()
        .1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    prepared.admit(&ops).unwrap()
}
#[test]
fn value_universe_presence_flags_and_repeated_predicate_uses_match_the_tutorial() {
    let p = Snapshot::new(9).load();
    let prepared = prepared(&p);
    let program = prepared.program();
    let flag = atom(
        &p,
        "shipping::element_value",
        &["shipment::fragile", "shipping::flags::true"],
    );
    let no_flag = atom(
        &p,
        "shipping::element_value",
        &["shipment::fragile", "shipping::flags::false"],
    );
    let inputs = program.input_atoms().cloned().collect::<BTreeSet<_>>();
    assert!(inputs.contains(&flag) && inputs.contains(&no_flag));
    assert!(!inputs.contains(&atom(
        &p,
        "shipping::field_value",
        &["carrier::service", "literals::standard"]
    )));
    assert!(inputs.contains(&atom(
        &p,
        "shipping::field_value",
        &["carrier::service", "other_values::text_other"]
    )));
    for (world, expected) in [
        (vec![], [false, false, true]),
        (vec![flag], [true, false, false]),
        (vec![no_flag], [false, true, true]),
    ] {
        let replay = program.evaluate(world, &Limits::default()).unwrap();
        for (rel, value) in [
            "feature_routes::$fragile",
            "feature_routes::$explicit_false",
            "feature_routes::$not_fragile",
        ]
        .into_iter()
        .zip(expected)
        {
            assert_eq!(
                replay.fact(&atom(&p, rel, &[])).unwrap(),
                FactState::Settled(value)
            );
        }
        // No value means neither positive check holds, but their negations do.
        assert_eq!(
            replay
                .fact(&atom(
                    &p,
                    "shipping::predicate_holds",
                    &["shipment::country", "checks::domestic"]
                ))
                .unwrap(),
            FactState::Settled(false)
        );
        // Unconditional UDF applicability does not require source presence.
        assert_eq!(
            replay
                .fact(&atom(
                    &p,
                    "shipping::applicable_inbound_mapping",
                    &["conversions::unpack"]
                ))
                .unwrap(),
            FactState::Settled(true)
        );
    }
}
#[test]
fn conditional_terms_and_recursion_match_an_independent_boolean_table() {
    let p = Snapshot::new(7).load();
    let prepared = prepared(&p);
    let program = prepared.program();
    // 4 toggle combinations × 3 flag states × 4 country/check states × 2 weight states.
    // Each world obeys the selected predicate contract; no solver-chosen witnesses.
    for toggles in 0..4 {
        for fragile in 0..3 {
            for country in 0..4 {
                for weight in [false, true] {
                    let mut world = Vec::new();
                    for (bit, name) in [
                        (1, "options::customs-checks"),
                        (2, "options::express-service"),
                    ] {
                        if toggles & bit != 0 {
                            world.push(atom(&p, "shipping::toggle_active", &[name]));
                        }
                    }
                    if fragile > 0 {
                        world.push(atom(
                            &p,
                            "shipping::element_value",
                            &[
                                "shipment::fragile",
                                if fragile == 1 {
                                    "shipping::flags::true"
                                } else {
                                    "shipping::flags::false"
                                },
                            ],
                        ));
                    }
                    if country > 0 {
                        world.push(atom(
                            &p,
                            "shipping::element_value",
                            &["shipment::country", "other_values::text_other"],
                        ));
                    }
                    if country >= 2 {
                        world.push(atom(
                            &p,
                            "shipping::predicate_result",
                            &[
                                "shipment::country",
                                if country == 2 {
                                    "checks::domestic"
                                } else {
                                    "checks::international"
                                },
                            ],
                        ));
                    }
                    if weight {
                        world.push(atom(
                            &p,
                            "shipping::element_value",
                            &["shipment::assessed_weight", "other_values::number_other"],
                        ));
                    }
                    let replay = program.evaluate(world, &Limits::default()).unwrap();
                    let rules =
                        toggles & 1 == 0 || (country >= 2 && (toggles & 2 == 0 || fragile == 2));
                    for (rel, value) in [
                        ("terms::dispatch_rules", rules),
                        ("terms::ready", weight && rules),
                        ("terms::attention", fragile == 1),
                        ("terms::follow_up", fragile == 1),
                        ("terms::self_guard", false),
                    ] {
                        assert_eq!(
                            replay.fact(&atom(&p, rel, &[])).unwrap(),
                            FactState::Settled(value),
                            "{rel}: {toggles}/{fragile}/{country}/{weight}"
                        );
                    }
                }
            }
        }
    }
}
#[test]
fn malformed_domain_metadata_and_predicate_uses_are_not_silently_filtered() {
    for (edit, verification) in [
        (
            "shipping::element_comparison(shipment::fragile, other_values::number_other);",
            "shipping::value_declarations",
        ),
        (
            "shipping::predicate_use(shipment::weight, checks::domestic);",
            "shipping::predicate_declarations",
        ),
        (
            "namespace extension { const date: shipping::DataType; }",
            "shipping::value_declarations",
        ),
    ] {
        let mut s = Snapshot::new(9);
        s.append(edit);
        let r = check(&s.load(), &mut Session::default());
        assert_eq!(r[verification].summary["state"], "findings");
    }
}
#[test]
fn repeated_mapping_counts_once_but_a_direct_converter_destination_collision_does_not() {
    let mut s = Snapshot::new(4);
    let p = s.load();
    let mut session = Session::default();
    assert_eq!(
        check(&p, &mut session)["shipping::mappings"].summary["state"],
        "proved"
    );
    s.replace(
        "converters.den",
        "inbound_result(unpack, unpack_mass::normalized, shipment::normalized_weight);",
        "inbound_result(unpack, unpack_mass::normalized, shipment::weight);",
    );
    let p = s.load();
    let warm = check(&p, &mut session);
    let cold = check(&p, &mut Session::default());
    assert_eq!(outcomes(&warm), outcomes(&cold));
    assert_eq!(warm["shipping::mappings"].summary["state"], "findings");
}

#[test]
fn opaque_checks_require_presence_share_uses_but_do_not_correlate_endpoints() {
    let mut s = Snapshot::new(9);
    s.append("shipping::predicate_use(shipment::country, checks::domestic); shipping::predicate_use(shipment::routing_note, checks::domestic); shipping::element_comparison(shipment::country, literals::express); shipping::element_comparison(shipment::routing_note, literals::express);");
    let p = s.load();
    let prepared = prepared(&p);
    let program = prepared.program();
    let result = atom(
        &p,
        "shipping::predicate_result",
        &["shipment::country", "checks::domestic"],
    );
    let truth = atom(
        &p,
        "shipping::predicate_holds",
        &["shipment::country", "checks::domestic"],
    );
    let replay = program
        .evaluate([result.clone()], &Limits::default())
        .unwrap();
    assert_eq!(replay.fact(&truth).unwrap(), FactState::Settled(false));
    // Repeated authored calls use this same input atom. No second call bit exists.
    assert_eq!(program.input_atoms().filter(|a| **a == result).count(), 1);
    let replay = program
        .evaluate(
            [
                result,
                atom(
                    &p,
                    "shipping::element_value",
                    &["shipment::country", "literals::express"],
                ),
                atom(
                    &p,
                    "shipping::element_value",
                    &["shipment::routing_note", "literals::express"],
                ),
            ],
            &Limits::default(),
        )
        .unwrap();
    assert_eq!(replay.fact(&truth).unwrap(), FactState::Settled(true));
    assert_eq!(
        replay
            .fact(&atom(
                &p,
                "shipping::predicate_holds",
                &["shipment::routing_note", "checks::domestic"]
            ))
            .unwrap(),
        FactState::Settled(false)
    );
}

#[test]
fn overlapping_disjoint_families_do_not_imply_transitivity() {
    let mut s = Snapshot::new(6);
    s.append("use shipping; namespace extra { const remote: Predicate; predicate_type(remote,text); predicate_use(shipment::country,remote); const zone: DisjointFamily; disjoint_member(zone,checks::international); disjoint_member(zone,remote); }");
    let p = s.load();
    let prepared = prepared(&p);
    let program = prepared.program();
    for checks in [
        vec![],
        vec!["checks::domestic"],
        vec!["checks::international"],
        vec!["extra::remote"],
        vec!["checks::domestic", "extra::remote"],
    ] {
        let mut world = vec![atom(
            &p,
            "shipping::element_value",
            &["shipment::country", "other_values::text_other"],
        )];
        world.extend(
            checks
                .into_iter()
                .map(|c| atom(&p, "shipping::predicate_result", &["shipment::country", c])),
        );
        assert!(program.evaluate(world, &Limits::default()).is_ok());
    }
    for partner in ["checks::domestic", "extra::remote"] {
        let world = [
            atom(
                &p,
                "shipping::element_value",
                &["shipment::country", "other_values::text_other"],
            ),
            atom(
                &p,
                "shipping::predicate_result",
                &["shipment::country", "checks::international"],
            ),
            atom(
                &p,
                "shipping::predicate_result",
                &["shipment::country", partner],
            ),
        ];
        assert!(matches!(
            program.evaluate(world, &Limits::default()),
            Err(CheckError::InvalidInputGroup(_))
        ));
    }
}
