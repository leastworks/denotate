use denotate_check::{GroundAtom, Limits, completion_query::*};
use denotate_ir_text::*;
fn loaded(text: &str) -> LoadedProgram {
    let s = SourceFile::new("file:///planning.den", 1, text);
    load(&ProgramMembership::single("root", [s.uri.clone()]), &[s]).unwrap()
}
fn engine(p: &LoadedProgram, queries: QueryLimits) -> Engine {
    let v = p.corpus.verifications().next().unwrap().id;
    let Preparation::Ready(e) = Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        queries,
    )
    .unwrap() else {
        panic!()
    };
    e
}
fn atom(p: &LoadedProgram, name: &str) -> GroundAtom {
    GroundAtom::new(
        p.corpus.relations().find(|r| r.name == name).unwrap().id,
        [],
    )
}
const V: &str =
    "verification v{semantics:completion;hypothesis:h;decisions:[];assumptions:[];obligations:[];}";
#[test]
fn hypothesis_constant_does_not_erase_runtime_rejection() {
    let p = loaded(&format!("input raw();relation h();h():-raw();{V}"));
    let e = engine(&p, Default::default());
    let options = CheckOptions::default();
    assert_eq!(
        e.planning_context(&RuntimePath::new(), &options)
            .unwrap()
            .outcome,
        PathOutcome::Mixed
    );
    assert!(matches!(
        e.planning_constant(
            &RuntimePath::new(),
            &atom(&p, "raw"),
            ConstantScope::Classification,
            &options
        )
        .unwrap(),
        PlanningConstant::Proven { value: true, .. }
    ));
    for value in [false, true] {
        let path = RuntimePath::from([(atom(&p, "raw"), value)]);
        let expected = if value {
            PathOutcome::Accept
        } else {
            PathOutcome::Reject
        };
        for e in [&e, &engine(&p, Default::default())] {
            assert_eq!(
                e.planning_context(&path, &options).unwrap().outcome,
                expected
            );
            if !value {
                assert!(
                    matches!(e.planning_constant(&path,&atom(&p,"h"),ConstantScope::Classification,&options).unwrap(),PlanningConstant::ContextNotReady(c) if c.outcome==PathOutcome::Reject)
                );
            }
        }
    }
    assert!(
        e.planning_context(&RuntimePath::from([(atom(&p, "h"), true)]), &options)
            .is_err()
    );
}
#[test]
fn completion_constants_helpers_and_downstream_scopes_remain_separate() {
    let p = loaded(&format!(
        "relation p();p():-p();relation h();h():-p();relation helper();helper():-helper();relation broken();broken():-!broken();{V}"
    ));
    let e = engine(&p, Default::default());
    let path = RuntimePath::new();
    let opts = CheckOptions::default();
    assert_eq!(
        e.planning_context(&path, &opts).unwrap().outcome,
        PathOutcome::Accept
    );
    assert!(matches!(
        e.planning_constant(&path, &atom(&p, "p"), ConstantScope::Classification, &opts)
            .unwrap(),
        PlanningConstant::Proven { value: true, .. }
    ));
    assert!(matches!(
        e.planning_constant(&path, &atom(&p, "helper"), ConstantScope::Output, &opts)
            .unwrap(),
        PlanningConstant::Varying(_)
    ));
    assert!(matches!(
        e.planning_constant(&path, &atom(&p, "broken"), ConstantScope::Output, &opts)
            .unwrap(),
        PlanningConstant::NoInterpretation
    ));
    assert!(
        e.planning_constant(
            &path,
            &atom(&p, "helper"),
            ConstantScope::Classification,
            &opts
        )
        .is_err()
    );
}
#[test]
fn invalid_contract_and_empty_worlds_do_not_prove_constants() {
    for (definition, expected) in [
        ("a():-a();", PathOutcome::Invalid),
        ("", PathOutcome::NoPermittedInputs),
    ] {
        let p = loaded(&format!(
            "relation a();{definition}relation h();h();assumption valid:at_least_one(a,group_by:());verification v{{semantics:completion;hypothesis:h;decisions:[];assumptions:[valid];obligations:[];}}"
        ));
        let e = engine(&p, Default::default());
        assert_eq!(
            e.planning_context(&RuntimePath::new(), &Default::default())
                .unwrap()
                .outcome,
            expected
        );
        assert!(matches!(
            e.planning_constant(
                &RuntimePath::new(),
                &atom(&p, "h"),
                ConstantScope::Classification,
                &Default::default()
            )
            .unwrap(),
            PlanningConstant::ContextNotReady(_)
        ));
    }
}
#[test]
fn exhausted_path_query_is_inconclusive_and_does_not_contaminate_fresh_queries() {
    let p = loaded(&format!("input raw();relation h();h():-raw();{V}"));
    let e = engine(
        &p,
        QueryLimits {
            max_solves: 0,
            ..Default::default()
        },
    );
    assert_eq!(
        e.planning_context(&RuntimePath::new(), &Default::default())
            .unwrap()
            .outcome,
        PathOutcome::Inconclusive
    );
    assert_eq!(
        engine(&p, Default::default())
            .planning_context(&RuntimePath::new(), &Default::default())
            .unwrap()
            .outcome,
        PathOutcome::Mixed
    );
}
#[test]
fn runtime_outcome_matches_exhaustive_equations_including_reject_and_no_meaning() {
    let bodies = ["raw()", "!raw()", "p()", "!p()", "q()", "!q()"];
    let eval = |i: usize, raw: bool, p: bool, q: bool| [raw, !raw, p, !p, q, !q][i];
    for (i, a) in bodies.iter().enumerate() {
        for (j, b) in bodies.iter().enumerate() {
            let p = loaded(&format!(
                "input raw();relation p();relation q();p():-{a};q():-{b};relation h();h():-p(),q();{V}"
            ));
            let e = engine(&p, Default::default());
            for raw in [false, true] {
                let models: Vec<_> = (0..4)
                    .filter(|bits| {
                        let pv = bits & 1 != 0;
                        let qv = bits & 2 != 0;
                        pv == eval(i, raw, pv, qv) && qv == eval(j, raw, pv, qv)
                    })
                    .collect();
                let expected = if models.contains(&3) {
                    PathOutcome::Accept
                } else if models.is_empty() {
                    PathOutcome::Invalid
                } else {
                    PathOutcome::Reject
                };
                let actual = e
                    .planning_context(
                        &RuntimePath::from([(atom(&p, "raw"), raw)]),
                        &Default::default(),
                    )
                    .unwrap();
                assert_eq!(actual.outcome, expected, "{a}, {b}, raw={raw}");
            }
        }
    }
}
