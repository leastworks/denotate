use crate::Session;
use denotate_check::*;
use denotate_ir_text::{LoadedProgram, ProgramMembership, SourceFile, load};
use std::collections::BTreeMap;

fn run(
    p: &LoadedProgram,
    session: &mut Session,
    folded: bool,
) -> (BTreeMap<LocalScope, LocalInput>, Accounted<ScopedResults>) {
    let limits = Limits::default();
    let operations = (&limits).into();
    let request = p.verification_requests(&limits).unwrap().pop().unwrap().1;
    let prepared = if folded {
        let fixed = session
            .prepare_fixed(&p.corpus, &p.keys, &p.domains, &limits)
            .unwrap();
        session
            .prepare_with_fixed(&request, &p.corpus, &p.keys, &operations, &fixed)
            .unwrap()
    } else {
        request.prepare(&p.corpus, &p.keys, &operations).unwrap()
    };
    let RequestPreparation::Complete(prepared) = prepared else {
        panic!("preparation exhausted")
    };
    let prepared = prepared.admit(&operations).unwrap();
    assert!(prepared.program().admission_limit().is_none());
    assert!(
        prepared
            .program()
            .rewrite_proofs()
            .any(|p| p.symbolic().is_some_and(|p| p.upper_bounds.is_some()))
    );
    assert!(
        prepared
            .program()
            .rewrite_proofs()
            .any(|p| p.kind == RewriteKind::RedundantProducer)
    );
    if folded {
        assert!(prepared.program().fixed_size().0 > 0);
    }
    let LocalCheckOutcome::Complete(report) = session.verify(&prepared, &operations).unwrap()
    else {
        panic!("checking exhausted")
    };
    let context = prepared.program().condition_context(&limits).unwrap();
    assert!(
        report
            .queries
            .values()
            .any(|q| q.input.completion_context.is_some())
    );
    assert!(
        report
            .queries
            .values()
            .any(|q| q.input.original_dependencies.len() > q.input.rules.len())
    );
    for (scope, artifact) in &report.queries {
        let roots = artifact
            .input
            .roots
            .iter()
            .map(|a| prepared.key_view().bind_atom(a).unwrap());
        let cone = prepared.program().dependency_cone(roots, &limits).unwrap();
        assert_eq!(
            artifact.input,
            prepared
                .local_input_scanning_reference(scope.clone(), &cone, &context)
                .unwrap()
        );
    }
    (
        report
            .queries
            .into_iter()
            .map(|(s, a)| (s, a.input))
            .collect(),
        report.checked.results,
    )
}

#[test]
fn query_input_index_preserves_folded_originals_discharge_context_and_dropped_alternatives() {
    let mut source = String::from("sort S; const left,right:S; input on(); input choice(s:S);\n");
    // Declare the chain in consumer-first order, with fixed evidence behind it.
    for i in 0..16 {
        source.push_str(&format!(
            "relation fixed{i}(); fixed{i}():-fixed{}();\n",
            i + 1
        ));
    }
    source.push_str(
        "relation stable(); stable(); relation fixed16(); fixed16();
relation a(); relation b(); a():-on(),!b(); b():-!on(),!a();
relation u(); relation v(); u():-!v(); v():-!u();
relation out(s:S); out(left):-a(),fixed0(); out(right):-b(),fixed0();
out(left):-on(),u(); out(right):-!on(),u();
relation odd(); odd():-a(),!odd();
assumption exclusive:at_most_one(choice,group_by:());
obligation unique_out:at_most_one(out,group_by:());
verification checks{assumptions:[exclusive];obligations:[unique_out];}",
    );
    for folded in [false, true] {
        let mut warm = Session::default();
        for (revision, text) in [
            source.clone(),
            format!("// moved\n{source}"),
            source.replace("fixed16();\nrelation a", "fixed16():-on();\nrelation a"),
            source.replace("assumptions:[exclusive]", "assumptions:[]"),
            source.clone(),
        ]
        .into_iter()
        .enumerate()
        {
            let file = SourceFile::new(
                format!("file:///revision-{revision}/query.den"),
                revision as u64,
                text,
            );
            let p = load(
                &ProgramMembership::single("root", [file.uri.clone()]),
                &[file],
            )
            .unwrap();
            let cold = run(&p, &mut Session::default(), folded);
            let current = run(&p, &mut warm, folded);
            assert_eq!(cold, current);
            assert_eq!(current, run(&p, &mut warm, folded));
            // Folded and unfolded logical receipts deliberately differ; compare
            // current meanings, while same-mode cold/warm includes receipts.
            assert_eq!(
                current.1.value,
                run(&p, &mut Session::default(), !folded).1.value
            );
        }
    }
}
