use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir_text::*;
use std::collections::BTreeSet;

const BASE: &str = include_str!("fixtures/bound-removal.den");
fn source(version: u8, restricted: bool) -> String {
    let text = match version {
        1 => BASE.replace("kept() :- !possible_without();", ""),
        2 => BASE.into(),
        3 => BASE.replace(
            "unsat_c() :- !kind(q);",
            "unsat_c() :- !kind(q);\nunsat_c() :- term_a();",
        ),
        4 => BASE.replace("kept() :- required();", ""),
        _ => unreachable!(),
    };
    if restricted {
        text
    } else {
        text.replace("assumptions: [one_kind]", "assumptions: []")
    }
}
fn loaded(text: String, revision: u64) -> LoadedProgram {
    let doc = SourceFile::new("file:///bounds.den", revision, text);
    load(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
    )
    .unwrap()
}

#[test]
fn exact_guarantees_admit_the_two_redundant_cycles_but_not_the_ambiguous_variants() {
    use test_support::rewrites::{compare_permitted, subsets, supported_models};
    for (version, restricted, admitted) in [
        (1, true, false),
        (2, true, true),
        (3, true, true),
        (4, true, true),
        (2, false, false),
    ] {
        let p = loaded(source(version, restricted), 0);
        let limits = Limits::default();
        let ops = (&limits).into();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let RequestPreparation::Complete(prepared) =
            request.prepare(&p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!()
        };
        let prepared = prepared.admit(&ops).unwrap();
        let ground = prepared.program();
        assert_eq!(
            ground.is_admitted(),
            admitted,
            "v{version}, restricted={restricted}: {:?}",
            ground.admission_limit()
        );
        assert!(ground.admission_limit().is_none());
        let kind = p.corpus.relations().find(|r| r.name == "kind").unwrap().id;
        let permitted = |world: &BTreeSet<GroundAtom>| {
            !restricted || world.iter().filter(|a| a.relation == kind).count() == 1
        };
        assert!(compare_permitted(&p.corpus, &p.domains, ground, permitted) > 0);
        for world in subsets(&ground.input_atoms().cloned().collect::<Vec<_>>())
            .into_iter()
            .filter(permitted)
        {
            assert_eq!(
                supported_models(
                    ground,
                    &ground.original_rules().cloned().collect::<Vec<_>>(),
                    &world
                ),
                supported_models(ground, &ground.rules().cloned().collect::<Vec<_>>(), &world)
            );
        }
        let bounds: Vec<_> = ground
            .rewrite_proofs()
            .filter_map(|p| p.bound_removal())
            .collect();
        if restricted && (version == 2 || version == 3) {
            assert!(!bounds.is_empty(), "v{version}");
            for proof in bounds {
                assert!(!proof.proof.candidate.exact);
                assert!(proof.proof.producers.iter().all(|p| p.exact));
            }
            let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
                panic!()
            };
            let direct = presentation::present(&p, &report).unwrap();
            let full = presentation::present_with_rewrite_detail(
                &p,
                &report,
                presentation::RewriteDetail::Full,
            )
            .unwrap();
            assert_eq!(direct.status, full.status);
            let warnings: Vec<_> = direct
                .diagnostics
                .iter()
                .filter(|d| d.evidence["boundDetail"] == "direct")
                .collect();
            assert!(!warnings.is_empty());
            assert!(
                warnings
                    .iter()
                    .all(|d| d.notes.iter().any(|n| n.contains("Bound proof")))
            );
            assert!(warnings.iter().all(|d| {
                d.related
                    .iter()
                    .any(|r| r.label == "direct rewrite justification")
            }));
            for d in warnings {
                let f = full
                    .diagnostics
                    .iter()
                    .find(|f| f.identity == d.identity && f.primary == d.primary)
                    .unwrap();
                assert_eq!(f.evidence["boundDetail"], "full");
                assert!(f.related.len() > d.related.len());
            }
        }
    }
}

#[test]
fn bound_removals_match_fresh_cold_warm_folded_and_edited_contexts() {
    let mut warm = Session::default();
    let local = source(3, true)
        .replace("exactly_one(kind", "at_most_one(kind")
        .replace("obligations: [exclusive_terms]", "obligations: [unique]")
        + "\nconst extra: Value; relation out(v: Value); out(ten) :- term_a(); out(extra) :- kind(p); obligation unique: at_most_one(out, group_by: ());";
    for (revision, text) in [
        source(3, true),
        local.clone(),
        // Change a transitive bound guarantee while the direct cover stays put.
        local.replace("unsat_a() :- !kind(p);", "unsat_a() :- !received(ten);"),
        local,
        format!("// moved\n{}", source(3, true)),
        source(3, false),
        source(1, true),
        source(3, true),
    ]
    .into_iter()
    .enumerate()
    {
        let p = loaded(text, revision as u64);
        let limits = Limits::default();
        let ops = (&limits).into();
        let request = p.verification_requests(&limits).unwrap().remove(0).1;
        let run = |mut session: Option<&mut Session>| {
            let prepared = if let Some(s) = session.as_deref_mut() {
                let fixed = s
                    .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
                    .unwrap();
                s.prepare_with_fixed(&request, &p.corpus, &p.keys, &ops, &fixed)
            } else {
                request.prepare(&p.corpus, &p.keys, &ops)
            }
            .unwrap();
            let RequestPreparation::Complete(prepared) = prepared else {
                panic!()
            };
            let prepared = prepared.admit(&ops).unwrap();
            let checked = if let Some(s) = session {
                s.verify(&prepared, &ops)
            } else {
                prepared.verify_local(&ops)
            }
            .unwrap();
            let LocalCheckOutcome::Complete(report) = checked else {
                panic!()
            };
            let shown = presentation::present(&p, &report.checked).unwrap();
            let details:Vec<_>=shown.diagnostics.iter().map(|d|serde_json::json!({"data":d.data(&p.keys).unwrap(),"notes":d.notes,"primary":p.sources.text(d.primary).unwrap(),"related":d.related.iter().map(|r|(p.sources.text(r.span).unwrap(),&r.label)).collect::<Vec<_>>()})).collect();
            (report.checked.results.value, shown.status, details)
        };
        let fresh = run(None);
        assert_eq!(run(Some(&mut Session::default())), fresh);
        assert_eq!(run(Some(&mut warm)), fresh);
        assert_eq!(run(Some(&mut warm)), fresh);
    }
}

#[test]
fn bound_warning_details_are_bounded_after_union_and_expand_explicitly() {
    let n = 40;
    let mut text = format!(
        "sort S; const {}: S; input chosen(s:S); relation a(s:S); relation b(s:S); relation kept(s:S);\n",
        (0..n)
            .map(|i| format!("i{i:03}"))
            .collect::<Vec<_>>()
            .join(",")
    );
    text += "relation member(s:S);\n";
    for i in 0..n {
        text += &format!("member(i{i:03});\n");
        text += &format!("kept(i{i:03}) :- chosen(i{i:03});\n");
    }
    text += "a(X) :- member(X), !b(X); b(X) :- member(X), !chosen(X); b(X) :- member(X), !kept(X); kept(X) :- a(X); verification checks { assumptions: []; obligations: []; }";
    let p = loaded(text, 0);
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let RequestPreparation::Complete(prepared) = request.prepare(&p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let prepared = prepared.admit(&ops).unwrap();
    assert!(prepared.program().is_admitted());
    let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
        panic!()
    };
    let direct = presentation::present(&p, &report).unwrap();
    let full =
        presentation::present_with_rewrite_detail(&p, &report, presentation::RewriteDetail::Full)
            .unwrap();
    let warning = direct
        .diagnostics
        .iter()
        .find(|d| p.sources.text(d.primary).unwrap() == "kept(X) :- a(X);")
        .unwrap();
    let expanded = full
        .diagnostics
        .iter()
        .find(|d| d.identity == warning.identity)
        .unwrap();
    assert_eq!(warning.evidence["boundDetail"], "direct");
    assert_eq!(
        warning.notes.len(),
        denotate_presentation::STRUCTURAL_NOTE_LIMIT + 1
    );
    assert_eq!(
        warning.evidence["omittedNotes"],
        n - denotate_presentation::STRUCTURAL_NOTE_LIMIT
    );
    assert_eq!(
        warning.related.len(),
        denotate_presentation::STRUCTURAL_LOCATION_LIMIT
    );
    assert_eq!(
        warning.evidence["omittedRelatedLocations"],
        n - denotate_presentation::STRUCTURAL_LOCATION_LIMIT
    );
    assert_eq!(expanded.evidence["boundDetail"], "full");
    assert_eq!(expanded.evidence["omittedNotes"], 0);
    assert_eq!(expanded.notes.len(), n);
    assert_eq!(direct.status, full.status);
}
