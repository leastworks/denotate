use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load, presentation};

fn program(width: usize, revision: u64) -> LoadedProgram {
    let mut text = String::from("relation wide();\n");
    for i in 0..8 {
        text.push_str(&format!("input input_{i}();\n"));
        if i < width {
            text.push_str(&format!("wide() :- input_{i}();\n"));
        }
    }
    text.push_str("relation never(); never() :- input_0(), !input_0();\nrelation safe(); safe() :- wide(), never();\nrelation reader(); reader() :- !wide();\nsort V; const a,b: V; relation choices(v:V); choices(a) :- wide(); choices(b) :- input_0();\nobligation safe_empty: empty(safe); obligation dependent_empty: empty(reader); obligation unique: at_most_one(choices, group_by: ()); obligation covered: at_least_one(choices, group_by: ());\nverification checks { assumptions: []; obligations: [safe_empty, dependent_empty, unique, covered]; }\n");
    let file = SourceFile::new("file:///symbolic-exhaustion.den", revision, text);
    load(
        &ProgramMembership::single("root", [file.uri.clone()]),
        &[file],
    )
    .unwrap()
}

fn check(p: &LoadedProgram, session: Option<&mut Session>, limited: bool) -> ScopedResults {
    let limits = Limits {
        max_bdd_nodes: if limited { 5 } else { 100_000 },
        ..Limits::default()
    };
    let operations = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    let RequestPreparation::Complete(prepared) =
        request.prepare(&p.corpus, &p.keys, &operations).unwrap()
    else {
        panic!("preparation")
    };
    let prepared = prepared.admit(&operations).unwrap();
    assert!(prepared.program().admission_limit().is_none());
    let report = if let Some(session) = session {
        let LocalCheckOutcome::Complete(r) = session.verify(&prepared, &operations).unwrap() else {
            panic!("local checking")
        };
        r.checked
    } else {
        let CheckOutcome::Complete(r) = prepared.verify(&operations).unwrap() else {
            panic!("checking")
        };
        r
    };
    let result = &report.results.value;
    let safe = p
        .corpus
        .obligations()
        .find(|o| o.name.as_str() == "safe_empty")
        .unwrap();
    assert!(result.emptiness[p.keys.obligation(safe.id).unwrap()].proved());
    if !result.unknown_atoms.is_empty() {
        assert!(result.emptiness.values().any(|e| e.inconclusive.is_some()));
        assert!(
            result
                .groups
                .values()
                .all(|g| matches!(g, ScopedResult::Inconclusive(_)))
        );
        assert!(
            result
                .coverage
                .values()
                .all(|c| c.inconclusive.is_some() && c.missing == 0)
        );
        let displayed = presentation::present(p, &report).unwrap();
        assert!(
            displayed.status["unknownAtoms"]
                .as_array()
                .is_some_and(|a| !a.is_empty())
        );
        assert!(displayed.diagnostics.iter().any(|d| {
            d.notes
                .iter()
                .any(|n| n.contains("wide()") && n.contains("BDD nodes"))
        }));
    }
    report.results.value
}

#[test]
fn symbolic_unknowns_are_keyed_reused_and_retried_after_a_producer_edit() {
    let mut warm = Session::default();
    for (revision, width) in [8, 8, 1, 8].into_iter().enumerate() {
        let p = program(width, revision as u64);
        let fresh = check(&p, None, true);
        assert_eq!(fresh.unknown_atoms.is_empty(), width == 1);
        assert_eq!(fresh, check(&p, Some(&mut Session::default()), true));
        assert_eq!(fresh, check(&p, Some(&mut warm), true));
        assert_eq!(fresh, check(&p, Some(&mut warm), true));
    }
    let p = program(8, 10);
    let unlimited = check(&p, None, false);
    assert!(unlimited.unknown_atoms.is_empty());
    assert_eq!(unlimited, check(&p, Some(&mut warm), false));
}
