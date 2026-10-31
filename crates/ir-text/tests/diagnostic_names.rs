use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::Term;
use denotate_ir_text::*;

fn program(text: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///names.den", 1, text);
    load(
        &ProgramMembership::single("root", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn checked<T>(p: &LoadedProgram, f: impl FnOnce(&CheckedReport<'_>) -> T) -> T {
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    let request = p.verification_requests(&limits).unwrap().remove(0).1;
    let mut session = Session::default();
    let RequestPreparation::Complete(prepared) =
        session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
    else {
        panic!()
    };
    let admitted = prepared.admit(&ops).unwrap();
    let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &ops).unwrap() else {
        panic!()
    };
    f(&report.checked)
}
fn notes(p: &LoadedProgram) -> Vec<String> {
    checked(p, |report| {
        presentation::present(p, report)
            .unwrap()
            .diagnostics
            .into_iter()
            .flat_map(|d| d.notes)
            .collect()
    })
}

#[test]
fn displayed_tuples_copy_back_to_the_same_declarations() {
    // Expectations deliberately come from source, independently of the printer.
    for name in [
        "plain",
        "'F3'",
        "'new-mode'",
        "'module'",
        "'a\\'b'",
        "'a\\\\b'",
        "'line\\n\\r\\t'",
        "'é'",
        "'007'",
        "'9223372036854775808'",
        "42",
        "-1",
    ] {
        for ns in ["", "'odd-space'::'namespace'::"] {
            let declarations = format!("const {name}: S; relation 'bad-result'(x:S);");
            let declarations = if ns.is_empty() {
                declarations
            } else {
                format!(
                    "namespace {} {{ {declarations} }}",
                    ns.trim_end_matches("::")
                )
            };
            let source = format!(
                "sort S; {declarations} {ns}'bad-result'({ns}{name}); obligation check: empty({ns}'bad-result'); verification checks {{ assumptions: []; obligations: [check]; }}"
            );
            let p = program(&source);
            let notes = notes(&p);
            let tuple = notes
                .iter()
                .find_map(|s| s.strip_prefix("Replayed present tuple: "))
                .unwrap()
                .strip_suffix('.')
                .unwrap();
            assert_eq!(tuple, format!("{ns}'bad-result'({ns}{name})"));
            // Put the displayed tuple in a new rule body: a bare uppercase constant
            // would become a variable here, even if loading happened to succeed.
            let copied = program(&format!("{source} relation probe(); probe() :- {tuple};"));
            let probe = copied
                .corpus
                .rules()
                .find(|r| copied.corpus.relation(r.head.relation()).unwrap().name == "probe")
                .unwrap();
            let original = copied
                .corpus
                .rules()
                .find(|r| copied.corpus.relation(r.head.relation()).unwrap().name == "bad-result")
                .unwrap();
            let atom = probe.body[0].atom();
            assert_eq!(atom.relation(), original.head.relation());
            assert!(matches!(atom.arguments()[0].value(), Term::Constant(_)));
            assert_eq!(
                atom.arguments()[0].value(),
                original.head.arguments()[0].value()
            );
        }
    }
}

#[test]
fn coverage_uniqueness_and_no_meaning_notes_use_source_names() {
    let declarations =
        "sort S; const 'F3', 'new-mode':S; input 'input-value'(x:S); relation r(x:S);";
    for (body, obligation, expected) in [
        (
            "r(X) :- 'input-value'(X);",
            "at_least_one(r, group_by: (x))",
            vec!["Missing group ('F3').", "'input-value'('F3')"],
        ),
        (
            "r('F3') :- 'input-value'('new-mode'); r('new-mode') :- 'input-value'('new-mode');",
            "at_most_one(r, group_by: ())",
            vec![
                "Replayed tuples: r('F3'), r('new-mode').",
                "'input-value'('new-mode')",
            ],
        ),
        (
            "r('F3') :- 'input-value'('new-mode'), !r('F3');",
            "empty(r)",
            vec!["Example input observation", "'input-value'('new-mode')"],
        ),
    ] {
        let p = program(&format!(
            "{declarations} {body} obligation check: {obligation}; verification checks {{ assumptions: []; obligations: [check]; }}"
        ));
        let notes = notes(&p).join("\n");
        for text in expected {
            assert!(notes.contains(text), "missing {text:?}: {notes}");
        }
    }
}

#[test]
fn spelling_does_not_affect_finding_identity_or_structured_evidence() {
    let p = program(
        "sort S; const 'F3':S; relation r(x:S); r('F3'); obligation check: empty(r); verification checks { assumptions: []; obligations: [check]; }",
    );
    checked(&p, |report| {
        let names = presentation::diagnostic_names(&p.corpus);
        let actual =
            denotate_presentation::interpret(&p.corpus, &report.verification, &names).unwrap();
        let renamed = denotate_presentation::interpret(&p.corpus, &report.verification, &|_| {
            "different display".into()
        })
        .unwrap();
        assert_eq!(actual.len(), renamed.len());
        for (a, b) in actual.iter().zip(&renamed) {
            assert_eq!(
                a.identity.data(&p.keys).unwrap(),
                b.identity.data(&p.keys).unwrap()
            );
            assert_eq!(
                denotate_presentation::evidence_data(a, &p.keys).unwrap(),
                denotate_presentation::evidence_data(b, &p.keys).unwrap()
            );
            assert_ne!(a.placement_groups[0].notes, b.placement_groups[0].notes);
        }
    });
}

#[test]
fn generated_and_authored_helper_names_remain_distinct() {
    let p = program("namespace 'helper-space' { relation $helper(); relation '$helper'(); }");
    let names = presentation::diagnostic_names(&p.corpus);
    for relation in p.corpus.relations() {
        let name = names(relation.id.into());
        let parsed = index::parse_name(&name).unwrap();
        assert_eq!(
            parsed.generated,
            p.corpus.is_generated_relation(relation.id)
        );
        assert_eq!(parsed.text, relation.name);
        assert_eq!(parsed.namespace.as_ref(), p.corpus.namespace(relation.id));
    }
}
