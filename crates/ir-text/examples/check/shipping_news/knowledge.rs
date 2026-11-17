use super::*;

#[path = "knowledge_cases.rs"]
mod cases;

// An independent three-valued evaluator: no .den gates, checker grounding,
// symbolic conditions or replay results enter this reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Truth {
    Unknown,
    False,
    True,
}
use Truth::{False, True, Unknown};
impl Truth {
    fn from_bool(value: bool) -> Self {
        if value { True } else { False }
    }
    fn not(self) -> Self {
        match self {
            True => False,
            False => True,
            Unknown => Unknown,
        }
    }
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (False, _) | (_, False) => False,
            (True, True) => True,
            _ => Unknown,
        }
    }
    fn read(self, observation: bool) -> Self {
        match self {
            Unknown => Unknown,
            False => False,
            True => Self::from_bool(observation),
        }
    }
    fn or(self, other: Self) -> Self {
        self.not().and(other.not()).not()
    }
}
const INPUTS: [(&str, &str); 7] = [
    ("direction", "request"),
    ("direction", "response"),
    ("request_kind", "booking"),
    ("request_kind", "cancellation"),
    ("response_kind", "booking"),
    ("response_kind", "cancellation"),
    ("note", "text"),
];
const LEAVES: [&str; 4] = [
    "booking_request",
    "booking_response",
    "cancellation_request",
    "cancellation_response",
];
const FIELDS: [&str; 4] = ["direction", "request_kind", "response_kind", "note"];
const ACCEPT: [&str; 4] = [
    "accept_direction",
    "accept_request_kind",
    "accept_response_kind",
    "accept_note",
];
fn expects(leaf: usize, field: usize) -> bool {
    match field {
        0 => true,
        1 => leaf == 0 || leaf == 2,
        2 => leaf == 1 || leaf == 3,
        3 => leaf == 0,
        _ => unreachable!(),
    }
}
fn reference(raw: [bool; 7]) -> BTreeMap<&'static str, Truth> {
    let mut state = BTreeMap::new();
    loop {
        let get = |name: &str| state.get(name).copied().unwrap_or(Unknown);
        let mut next = BTreeMap::new();
        for (i, name) in [
            "raw_request",
            "raw_response",
            "raw_request_booking",
            "raw_request_cancellation",
            "raw_response_booking",
            "raw_response_cancellation",
            "raw_note",
        ]
        .into_iter()
        .enumerate()
        {
            next.insert(name, Truth::from_bool(raw[i]));
        }
        for (field, name) in ACCEPT.into_iter().enumerate() {
            let coverage = LEAVES.iter().enumerate().fold(True, |all, (leaf, name)| {
                all.and(if expects(leaf, field) {
                    True
                } else {
                    get(name).not()
                })
            });
            next.insert(name, coverage);
        }
        for (name, accept, input) in [
            ("request", "accept_direction", 0),
            ("response", "accept_direction", 1),
            ("request_booking", "accept_request_kind", 2),
            ("request_cancellation", "accept_request_kind", 3),
            ("response_booking", "accept_response_kind", 4),
            ("response_cancellation", "accept_response_kind", 5),
            ("note_present", "accept_note", 6),
        ] {
            next.insert(name, get(accept).read(raw[input]));
        }
        next.insert("note_absent", get("note_present").not());
        for (writer, direction, kind) in [
            ("set_request_booking", "request", "request_booking"),
            (
                "set_request_cancellation",
                "request",
                "request_cancellation",
            ),
            ("set_response_booking", "response", "response_booking"),
            (
                "set_response_cancellation",
                "response",
                "response_cancellation",
            ),
        ] {
            next.insert(writer, get(direction).and(get(kind)));
        }
        next.insert(
            "booking",
            get("set_request_booking").or(get("set_response_booking")),
        );
        next.insert(
            "cancellation",
            get("set_request_cancellation").or(get("set_response_cancellation")),
        );
        next.insert("not_booking", get("booking").not());
        next.insert("fallback_guard", get("not_booking").and(get("note_absent")));
        for (leaf, kind, direction) in [
            (LEAVES[0], "booking", "request"),
            (LEAVES[1], "booking", "response"),
            (LEAVES[2], "cancellation", "request"),
            (LEAVES[3], "cancellation", "response"),
        ] {
            next.insert(leaf, get(kind).and(get(direction)));
        }
        next.insert("any_booking", get(LEAVES[0]).or(get(LEAVES[1])));
        next.insert("any_cancellation", get(LEAVES[2]).or(get(LEAVES[3])));
        next.insert("recognized", get("any_booking").or(get("any_cancellation")));
        if next == state {
            return state;
        }
        assert!(
            state
                .iter()
                .all(|(k, v)| *v == Unknown || next.get(k) == Some(v))
        );
        state = next;
    }
}

fn prepared<'a>(p: &'a LoadedProgram, name: &str, limits: &Limits) -> PreparedCheck<'a> {
    let request = p
        .verification_requests(limits)
        .unwrap()
        .into_iter()
        .find(|(key, _)| key.0.name.as_ref() == name)
        .unwrap()
        .1;
    let RequestPreparation::Complete(prepared) =
        request.prepare(&p.corpus, &p.keys, &limits.into()).unwrap()
    else {
        panic!("preparation exhausted")
    };
    let admitted = prepared.admit(&limits.into()).unwrap();
    assert!(admitted.program().is_admitted());
    assert!(admitted.program().admission_limit().is_none());
    assert!(admitted.program().components().all(|c| c.cycle.is_none()));
    assert_eq!(admitted.program().rewrite_proofs().count(), 0);
    admitted
}
fn decision(p: &LoadedProgram, name: &str, polarity: bool) -> GroundAtom {
    atom(
        p,
        if polarity {
            "schema::known_true"
        } else {
            "schema::known_false"
        },
        &[&format!("decisions::{name}")],
    )
}
fn raw_atoms(p: &LoadedProgram) -> Vec<GroundAtom> {
    INPUTS
        .iter()
        .map(|(f, v)| {
            atom(
                p,
                "schema::raw_value",
                &[&format!("fields::{f}"), &format!("values::{v}")],
            )
        })
        .collect()
}

#[test]
fn step_11_knowledge_form_is_admitted_without_rewrites_at_default_and_raised_limits() {
    let (code, results) = cli(11);
    assert_eq!(code, 0);
    assert_eq!(results.len(), 2);
    for result in results.values() {
        assert_eq!(result["state"], "proved");
        assert_eq!(result["findings"], json!([]));
    }
    let p = Snapshot::new(11).load();
    for limits in [
        Limits::default(),
        Limits {
            max_structural_split_depth: 64,
            max_structural_split_leaves: 256,
            ..Limits::default()
        },
    ] {
        for name in ["propagation", "recognized_messages"] {
            prepared(&p, name, &limits);
        }
    }
}

#[test]
fn knowledge_matches_independent_propagation_in_every_tiny_world() {
    let p = Snapshot::new(11).load();
    let limits = Limits::default();
    let all = prepared(&p, "propagation", &limits);
    let recognized = prepared(&p, "recognized_messages", &limits);
    let inputs = raw_atoms(&p);
    assert_eq!(
        all.program()
            .input_atoms()
            .cloned()
            .collect::<BTreeSet<_>>(),
        inputs.iter().cloned().collect()
    );
    let (mut scalar, mut accepted) = (0, 0);
    for bits in 0..128 {
        let raw = std::array::from_fn(|i| bits & (1 << i) != 0);
        let world = inputs
            .iter()
            .zip(raw)
            .filter(|(_, yes)| *yes)
            .map(|(a, _)| a.clone())
            .collect::<Vec<_>>();
        let replay = all.program().evaluate(world.clone(), &limits);
        if (0..3).any(|i| raw[2 * i] && raw[2 * i + 1]) {
            assert!(matches!(replay, Err(CheckError::InvalidObservation(_))));
            continue;
        }
        scalar += 1;
        let replay = replay.unwrap();
        assert!(replay.is_complete());
        let expected = reference(raw);
        for (name, truth) in &expected {
            for (positive, value) in [(true, *truth == True), (false, *truth == False)] {
                assert_eq!(
                    replay.fact(&decision(&p, name, positive)).unwrap(),
                    FactState::Settled(value),
                    "world {bits}, {name}, positive={positive}"
                );
            }
        }
        assert!(expected.values().all(|v| *v != Unknown));
        for (field, accept) in FIELDS.into_iter().zip(ACCEPT) {
            assert_eq!(
                replay
                    .fact(&atom(
                        &p,
                        "schema::message_source",
                        &[&format!("fields::{field}")]
                    ))
                    .unwrap(),
                FactState::Settled(expected[accept] == True)
            );
        }
        for kind in ["booking", "cancellation"] {
            assert_eq!(
                replay
                    .fact(&atom(
                        &p,
                        "schema::set_value",
                        &["fields::category", &format!("values::{kind}")]
                    ))
                    .unwrap(),
                FactState::Settled(expected[kind] == True)
            );
        }
        let filtered = recognized.program().evaluate(world, &limits);
        if expected["recognized"] == True {
            accepted += 1;
            assert!(filtered.unwrap().is_complete());
        } else {
            assert_eq!(expected["recognized"], False);
            assert!(matches!(filtered, Err(CheckError::InvalidInputGroup(_))));
        }
    }
    assert_eq!((scalar, accepted), (54, 24));
}

fn failed(result: &Checked) -> BTreeSet<String> {
    result.summary["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|f| {
            let identity = &f["identity"];
            identity["obligation"][1]
                .as_str()
                .or_else(|| identity["group"]["obligation"][1].as_str())
                .map(str::to_owned)
        })
        .collect()
}

#[test]
fn undecided_classification_stays_visible_before_recognition_filters_worlds() {
    let mut s = Snapshot::new(11);
    let mut session = Session::with_grounding();
    let original = "both(set_request_booking, request, request_booking);";
    let circular = "const circular_booking_guard: Decision; both(circular_booking_guard, request, request_booking); both(set_request_booking, circular_booking_guard, booking);";
    for broken in [false, true, false] {
        if broken {
            s.replace("program.den", original, circular);
        } else if s.sources.iter().any(|s| s.text.contains(circular)) {
            s.replace("program.den", circular, original);
        }
        let p = s.load();
        let warm = check(&p, &mut session);
        assert_eq!(
            outcomes(&warm),
            outcomes(&check(&p, &mut Session::default()))
        );
        assert_eq!(
            failed(&warm["schema::propagation"]),
            if broken {
                BTreeSet::from(["no_unknown_decisions".to_owned()])
            } else {
                BTreeSet::new()
            }
        );
        assert_eq!(
            warm["schema::recognized_messages"].summary["state"],
            "proved"
        );
        if broken {
            let prep = prepared(&p, "propagation", &Limits::default());
            let inputs = raw_atoms(&p);
            let world = [inputs[0].clone(), inputs[2].clone()];
            let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
            for name in ["booking", "not_booking", "recognized"] {
                assert_eq!(
                    replay.fact(&decision(&p, name, true)).unwrap(),
                    FactState::Settled(false)
                );
                assert_eq!(
                    replay.fact(&decision(&p, name, false)).unwrap(),
                    FactState::Settled(false)
                );
            }
        }
    }
}

#[test]
fn knowledge_checks_same_value_writes_and_absent_message_ownership_separately() {
    for (field, value, violation) in [
        ("category", "booking", None),
        ("category", "cancellation", Some("at_most_one_set_value")),
        ("note", "text", Some("no_message_writes")),
    ] {
        let mut s = Snapshot::new(11);
        s.append(&format!("use schema; namespace extra {{ const duplicate: Statement; writer_guard(duplicate, decisions::set_request_booking); set_output(duplicate, fields::{field}, values::{value}); }}"));
        let p = s.load();
        let result = check(&p, &mut Session::default());
        assert_eq!(
            failed(&result["schema::propagation"]),
            violation.into_iter().map(str::to_owned).collect()
        );
        if field == "note" {
            let prepared = prepared(&p, "propagation", &Limits::default());
            let inputs = raw_atoms(&p);
            let replay = prepared
                .program()
                .evaluate([inputs[0].clone(), inputs[2].clone()], &Limits::default())
                .unwrap();
            assert_eq!(
                replay
                    .fact(&atom(&p, "schema::message_source", &["fields::note"]))
                    .unwrap(),
                FactState::Settled(true)
            );
            assert_eq!(
                replay.fact(&decision(&p, "note_present", false)).unwrap(),
                FactState::Settled(true)
            );
            assert_eq!(
                replay
                    .fact(&atom(
                        &p,
                        "schema::invalid_message_write",
                        &["extra::duplicate", "fields::note"]
                    ))
                    .unwrap(),
                FactState::Settled(true)
            );
        }
    }
}

#[test]
fn recognition_rejects_a_gap_below_a_matching_root_and_detects_overlapping_roots() {
    let mut gap = Snapshot::new(11);
    gap.replace(
        "program.den",
        "both(booking_request, booking, request);",
        "always_false(booking_request);",
    );
    let p = gap.load();
    let prep = prepared(&p, "propagation", &Limits::default());
    let inputs = raw_atoms(&p);
    let world = [inputs[0].clone(), inputs[2].clone()];
    let replay = prep
        .program()
        .evaluate(world.clone(), &Limits::default())
        .unwrap();
    assert_eq!(
        replay.fact(&decision(&p, "booking", true)).unwrap(),
        FactState::Settled(true)
    );
    assert_eq!(
        replay.fact(&decision(&p, "recognized", false)).unwrap(),
        FactState::Settled(true)
    );
    let filtered = prepared(&p, "recognized_messages", &Limits::default());
    assert!(matches!(
        filtered.program().evaluate(world, &Limits::default()),
        Err(CheckError::InvalidInputGroup(_))
    ));

    let mut overlap = Snapshot::new(11);
    overlap.replace(
        "program.den",
        "either(cancellation, set_request_cancellation, set_response_cancellation);",
        "same(cancellation, booking);",
    );
    let p = overlap.load();
    let result = check(&p, &mut Session::default());
    assert_eq!(
        failed(&result["schema::propagation"]),
        BTreeSet::from(["at_most_one_path".to_owned()])
    );
}

#[test]
fn raw_values_from_dropped_fields_cannot_change_the_fallback_guard() {
    let p = Snapshot::new(11).load();
    let prep = prepared(&p, "propagation", &Limits::default());
    let inputs = raw_atoms(&p);
    for extra in [vec![], vec![inputs[4].clone(), inputs[6].clone()]] {
        let mut world = vec![inputs[0].clone(), inputs[3].clone()];
        world.extend(extra);
        let replay = prep.program().evaluate(world, &Limits::default()).unwrap();
        for name in [
            "accept_response_kind",
            "accept_note",
            "note_present",
            "booking",
        ] {
            assert_eq!(
                replay.fact(&decision(&p, name, false)).unwrap(),
                FactState::Settled(true)
            );
        }
        for name in ["note_absent", "not_booking", "fallback_guard", "recognized"] {
            assert_eq!(
                replay.fact(&decision(&p, name, true)).unwrap(),
                FactState::Settled(true)
            );
        }
    }
}

#[test]
fn conflicting_knowledge_is_reported_even_when_propagation_is_admitted() {
    let mut s = Snapshot::new(11);
    s.append("schema::always_false(decisions::request);");
    let p = s.load();
    let results = check(&p, &mut Session::default());
    assert!(failed(&results["schema::propagation"]).contains("no_conflicting_knowledge"));
}

#[test]
fn positive_self_support_and_reasoning_by_cases_remain_unknown_in_knowledge_form() {
    let p = load(
        &ProgramMembership::single("probe", ["file:///probe.den".to_owned()]),
        &[SourceFile::new(
            "file:///probe.den",
            0,
            r#"
        namespace probe;
        relation p_true(); relation p_false();
        p_true() :- p_true(); p_false() :- p_false();
        relation a_true(); relation a_false(); relation b_true(); relation b_false();
        a_true() :- b_false(); a_false() :- b_true();
        b_true() :- a_false(); b_false() :- a_true();
        relation exhaustive_true(); relation exhaustive_false();
        exhaustive_true() :- a_true(); exhaustive_true() :- a_false();
        exhaustive_false() :- a_true(), a_false();
        relation missing(); missing() :- !exhaustive_true();
        obligation detected: empty(missing);
        verification inspect { assumptions: []; obligations: [detected]; }
    "#,
        )],
    )
    .unwrap();
    let prep = prepared(&p, "inspect", &Limits::default());
    let replay = prep.program().evaluate([], &Limits::default()).unwrap();
    // Independently, the strong-Kleene equations stay Unknown from the bottom.
    let (p_ref, a, b) = (Unknown, Unknown, Unknown);
    assert_eq!(p_ref, p_ref.and(True));
    assert_eq!((a, b), (b.not(), a.not()));
    assert_eq!(a.or(a.not()), Unknown);
    for name in [
        "p_true",
        "p_false",
        "a_true",
        "a_false",
        "b_true",
        "b_false",
        "exhaustive_true",
        "exhaustive_false",
    ] {
        assert_eq!(
            replay
                .fact(&atom(&p, &format!("probe::{name}"), &[]))
                .unwrap(),
            FactState::Settled(false)
        );
    }
}
