use denotate_check::*;
use denotate_ir_text::*;
use denotate_presentation::{
    Kind, RewriteDetail, STRUCTURAL_LOCATION_LIMIT, STRUCTURAL_NOTE_LIMIT,
};

fn program(source: &str) -> LoadedProgram {
    let doc = SourceFile::new(
        "file:///program.den",
        1,
        format!("{source}\nverification checks {{ assumptions: []; obligations: []; }}"),
    );
    load(
        &ProgramMembership::single("root", [doc.uri.clone()]),
        &[doc],
    )
    .unwrap()
}

fn inspect(
    source: &str,
    test: impl Fn(&LoadedProgram, &presentation::Presentation, &presentation::Presentation),
) {
    let p = program(source);
    let limits = Limits::default();
    let ops = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    for folded in [false, true] {
        let fixed = FixedPreparation::prepare(&p.corpus, &p.domains, &limits).unwrap();
        let RequestPreparation::Complete(prepared) = (if folded {
            request.prepare_with_fixed(&p.corpus, &p.keys, &ops, &fixed, None)
        } else {
            request.prepare(&p.corpus, &p.keys, &ops)
        })
        .unwrap() else {
            panic!()
        };
        let expansions = test_support::structural_support_expansions();
        let prepared = prepared.admit(&ops).unwrap();
        let keyed = prepared.key_view().rewrites().unwrap();
        assert!(!keyed.is_empty());
        let CheckOutcome::Complete(report) = prepared.verify(&ops).unwrap() else {
            panic!()
        };
        let direct = presentation::present(&p, &report).unwrap();
        assert_eq!(
            test_support::structural_support_expansions(),
            expansions,
            "ordinary checking, keys and presentation must never expand structural chains"
        );
        let full =
            presentation::present_with_rewrite_detail(&p, &report, RewriteDetail::Full).unwrap();
        assert!(test_support::structural_support_expansions() > expansions);
        assert_eq!(direct.status, full.status);
        let ids = |out: &presentation::Presentation| {
            out.diagnostics
                .iter()
                .map(|d| {
                    d.identity
                        .data_in(&p.keys, d.verification.as_ref())
                        .unwrap()
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(ids(&direct), ids(&full));
        test(&p, &direct, &full);
    }
}

#[test]
fn structural_direct_evidence_retains_true_false_and_both_dead_polarities() {
    // Keep the whole false chain in the cycle's provider cone. A purely
    // downstream chain now settles before phase B and need not get lint warnings.
    inspect("relation a(); relation b(); relation d(); relation dead(); relation after(); relation cycle();
        a(); b():-a(); d():-b(); d():-cycle(); cycle():-!d(),after(); dead():-!d(); after():-dead();",
        |p, direct, full| {
            let at = |out: &presentation::Presentation, text: &str| out.diagnostics.iter().find(|d| p.sources.text(d.primary).unwrap()==text).unwrap().notes.join("\n");
            assert!(at(direct,"d():-cycle();").contains("d() is structurally true through a settling producer"));
            assert!(at(direct,"cycle():-!d(),after();").contains("!d() cannot hold"));
            assert!(at(direct,"after():-dead();").contains("all producers are dead or removed"));
            let sources = |out: &presentation::Presentation| out.diagnostics.iter().find(|d| p.sources.text(d.primary).unwrap()=="d():-cycle();").unwrap().related.iter().map(|r|p.sources.text(r.span).unwrap()).collect::<Vec<_>>();
            assert!(sources(direct).contains(&"d():-b();"));
            assert!(!sources(direct).contains(&"a();"));
            assert!(sources(full).contains(&"a();"));
        });
}

#[test]
fn structural_false_recursion_reports_no_derivation_not_no_producer() {
    // The impossible alternative keeps the recursive tuple in sparse grounding;
    // concrete evaluation still has no finite derivation of p().
    inspect("relation t(); t(); relation p(); p():-p(); p():-!t(); relation u(); relation v(); relation h();
        u():-!v(); v():-!u(); h():-p(),u();", |p,direct,_| {
        let warning=direct.diagnostics.iter().find(|d|p.sources.text(d.primary).unwrap()=="h():-p(),u();").unwrap();
        let notes=warning.notes.join("\n");
        assert!(notes.contains("p() is structurally false with no derivation from its producers"),"{notes}");
        assert!(!notes.contains("no producer"));
        assert!(warning.related.iter().any(|r|p.sources.text(r.span).unwrap()=="p():-p();"));
    });
}

#[test]
fn structural_subsumption_shows_unfolded_definitions_and_settled_premises() {
    inspect("input i(); relation t(); t(); relation missing(); relation outer(); relation inner(); relation h(); relation u(); relation v();
        outer():-i(),t(),!missing(); inner():-outer(),u();
        h():-outer(); h():-inner(); u():-!v(); v():-!h();",
        |p,direct,_| {
            let warning=direct.diagnostics.iter().find(|d|p.sources.text(d.primary).unwrap()=="h():-inner();").unwrap();
            let notes=warning.notes.join("\n");
            assert!(notes.contains("unfolding single-producer"),"{notes}");
            assert!(notes.contains("t() is structurally true"),"{notes}");
            assert!(notes.contains("missing() is structurally false with no possible ground producer"),"{notes}");
            for text in ["h():-outer();","outer():-i(),t(),!missing();","inner():-outer(),u();","t();"] {
                assert!(warning.related.iter().any(|r|p.sources.text(r.span).unwrap()==text),"missing {text}");
            }
        });
}

#[test]
fn structural_warning_bounds_apply_after_union_with_exact_omission_counts() {
    let n = 40;
    let mut source = format!(
        "sort S; const {}: S; input chosen(s:S); relation kept(s:S); relation term(s:S); relation base(); base(); relation middle(); middle():-base();\n",
        (0..n)
            .map(|i| format!("i{i:03}"))
            .collect::<Vec<_>>()
            .join(",")
    );
    for i in 0..n {
        source += &format!("kept(i{i:03}):-middle();\n");
    }
    source += "kept(X):-term(X); term(X):-chosen(X),!kept(X);";
    inspect(&source, |p, direct, full| {
        let warning = direct
            .diagnostics
            .iter()
            .find(|d| p.sources.text(d.primary).unwrap() == "kept(X):-term(X);")
            .unwrap();
        assert_eq!(warning.kind, Kind::Rewrite);
        assert_eq!(warning.notes.len(), STRUCTURAL_NOTE_LIMIT + 1);
        assert_eq!(warning.evidence["omittedNotes"], n - STRUCTURAL_NOTE_LIMIT);
        assert_eq!(warning.related.len(), STRUCTURAL_LOCATION_LIMIT);
        assert_eq!(
            warning.evidence["omittedRelatedLocations"],
            n - STRUCTURAL_LOCATION_LIMIT
        );
        assert!(
            warning
                .notes
                .last()
                .unwrap()
                .contains("request full rewrite evidence")
        );
        let expanded = full
            .diagnostics
            .iter()
            .find(|d| d.identity == warning.identity)
            .unwrap();
        assert_eq!(expanded.notes.len(), n);
        assert_eq!(expanded.evidence["omittedNotes"], 0);
        assert_eq!(expanded.evidence["omittedRelatedLocations"], 0);
        assert!(
            expanded
                .related
                .iter()
                .any(|r| p.sources.text(r.span).unwrap() == "base();")
        );
    });
}
