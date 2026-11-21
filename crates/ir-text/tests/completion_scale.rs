use denotate_check::{Limits, completion_query::*};
use denotate_ir_text::*;

fn loaded(body: &str) -> LoadedProgram {
    let source = SourceFile::new("file:///scale.den", 1, body);
    load(
        &ProgramMembership::single("scale", [source.uri.clone()]),
        &[source],
    )
    .unwrap()
}
fn prepared(p: &LoadedProgram) -> Engine {
    let v = p.corpus.verifications().next().unwrap().id;
    match Engine::prepare(
        &p.corpus,
        &p.domains,
        &p.keys,
        v,
        &Limits::default(),
        QueryLimits::default(),
    )
    .unwrap()
    {
        Preparation::Ready(e) => e,
        Preparation::Unsupported(e) => panic!("{e:?}"),
        Preparation::Inconclusive(e) => panic!("{e:?}"),
    }
}
fn constants(n: usize) -> String {
    format!(
        "sort S;const {}:S;",
        (0..n)
            .map(|i| format!("c{i}"))
            .collect::<Vec<_>>()
            .join(",")
    )
}
#[test]
fn sparse_join_preserves_self_support_at_a_scale_that_exceeds_full_grounding() {
    let mut text = constants(600);
    text.push_str(
        "relation allowed(x:S,y:S);input raw(x:S,y:S) within allowed;relation p(x:S,y:S);",
    );
    for i in 0..600 {
        text.push_str(&format!("allowed(c{i},c{i});"));
    }
    text.push_str("p(X,Y):-p(X,Y),allowed(X,Y);relation h();h():-p(c0,c0);verification v{semantics:completion;hypothesis:h;decisions:[h];assumptions:[];obligations:[];}");
    let p = loaded(&text);
    let e = prepared(&p);
    let options = CheckOptions {
        max_worlds: 1,
        ..Default::default()
    };
    for e in [&e, &prepared(&p)] {
        let r = e.check(&p.keys, &options).unwrap();
        assert!(!r.is_incomplete());
        assert!(!r.has_failures());
        assert!(r.classification.as_ref().unwrap().accepted.exists());
        assert!(matches!(
            r.classification.as_ref().unwrap().rejected,
            Search::None
        ));
    }
}
#[test]
fn projected_original_dependencies_survive_dead_cartesian_producers() {
    let mut text = constants(100);
    text.push_str("relation r(x:S);r(X):-r(X);relation absent(x:S);relation h(x:S);h(X):-r(X),r(Y),absent(Z);relation recognized();recognized();recognized():-h(c0);verification v{semantics:completion;hypothesis:recognized;decisions:[r];assumptions:[];obligations:[];}");
    let p = loaded(&text);
    let r = prepared(&p)
        .check(&p.keys, &CheckOptions::default())
        .unwrap();
    assert!(!r.is_incomplete());
    let class = r.classification.unwrap();
    assert!(class.ambiguous.exists());
    assert!(matches!(class.accepted, Search::None));
    assert!(matches!(class.rejected, Search::None));
    assert!(matches!(class.no_meaning, Search::None));
}
#[test]
fn dead_producers_do_not_hide_original_assumption_or_provider_cycles() {
    for declarations in [
        "input raw(x:S) within p;verification v{semantics:completion;assumptions:[];obligations:[];}",
        "assumption a:empty(p);verification v{semantics:completion;assumptions:[a];obligations:[];}",
    ] {
        let p = loaded(&format!(
            "sort S;const a:S;relation missing(x:S);relation p(x:S);p(X):-p(X),missing(X);{declarations}"
        ));
        let v = p.corpus.verifications().next().unwrap().id;
        assert!(matches!(
            Engine::prepare(
                &p.corpus,
                &p.domains,
                &p.keys,
                v,
                &Limits::default(),
                QueryLimits::default()
            )
            .unwrap(),
            Preparation::Unsupported(_)
        ));
    }
}
