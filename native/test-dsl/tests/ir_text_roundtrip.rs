#[path = "../../ir-text/tests/support/mod.rs"]
mod correspondence;
mod support;
use denotate_check::*;
use denotate_check_session::Session;
use denotate_ir::*;
use denotate_ir_text::*;
use denotate_test_dsl::{
    export,
    lowering::{self, LoweredProgram, LoweringOutcome},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Status {
    Proved,
    Counterexample,
    Unsupported,
    Inconclusive(ResourceReason),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Completion {
    Clear,
    NoMeaning,
    Deferred,
    Inconclusive(ResourceReason),
}
type AtomIdentity = (usize, Vec<usize>);
#[derive(Debug, PartialEq, Eq)]
struct Outcomes {
    groups: BTreeMap<(usize, Vec<usize>), Status>,
    regions: BTreeMap<Vec<AtomIdentity>, (Status, Completion)>,
    incomplete: BTreeSet<Vec<AtomIdentity>>,
    unfinished: Option<ResourceReason>,
}
struct Index {
    constants: BTreeMap<ConstantKey, usize>,
    relations: BTreeMap<RelationKey, usize>,
    obligations: BTreeMap<ObligationKey, usize>,
}
impl Index {
    fn new(
        original: &Corpus,
        current: &Corpus,
        keys: &SemanticKeys,
        map: Option<&correspondence::Correspondence>,
    ) -> Self {
        let mapped = |id| map.map_or(id, |m| m.ids[&id]);
        Self {
            constants: original
                .constants()
                .enumerate()
                .map(|(i, a)| {
                    let b = current
                        .constants()
                        .find(|b| OccurrenceId::from(b.id) == mapped(a.id.into()))
                        .unwrap();
                    (keys.constant(b.id).unwrap().clone(), i)
                })
                .collect(),
            relations: original
                .relations()
                .enumerate()
                .map(|(i, a)| {
                    let b = current
                        .relations()
                        .find(|b| OccurrenceId::from(b.id) == mapped(a.id.into()))
                        .unwrap();
                    (keys.relation(b.id).unwrap().clone(), i)
                })
                .collect(),
            obligations: original
                .obligations()
                .enumerate()
                .map(|(i, a)| {
                    let b = current
                        .obligations()
                        .find(|b| OccurrenceId::from(b.id) == mapped(a.id.into()))
                        .unwrap();
                    (keys.obligation(b.id).unwrap().clone(), i)
                })
                .collect(),
        }
    }
    fn atom(&self, a: &AtomKey) -> AtomIdentity {
        (
            self.relations[&a.relation],
            a.arguments.iter().map(|k| self.constants[k]).collect(),
        )
    }
    fn region(&self, c: &ComponentKey) -> Vec<AtomIdentity> {
        let mut atoms = c.0.iter().map(|a| self.atom(a)).collect::<Vec<_>>();
        atoms.sort();
        atoms
    }
    fn status(s: &ScopedResult) -> Status {
        match s {
            ScopedResult::Proved => Status::Proved,
            ScopedResult::Counterexample(..) => Status::Counterexample,
            ScopedResult::Unsupported(_) => Status::Unsupported,
            ScopedResult::Inconclusive(r) => Status::Inconclusive(r.clone()),
        }
    }
    fn outcomes(&self, r: &ScopedResults) -> Outcomes {
        let mut groups = BTreeMap::new();
        for (obligation, domain) in &r.group_domains {
            let mut tuples = vec![vec![]];
            for values in &domain.domains {
                tuples = tuples
                    .iter()
                    .flat_map(|t| {
                        values.iter().map(move |v| {
                            let mut t = t.clone();
                            t.push(v.clone());
                            t
                        })
                    })
                    .collect();
            }
            for tuple in tuples {
                let key = GroupKey {
                    obligation: obligation.clone(),
                    tuple: tuple.clone(),
                };
                let status = r.group(&key).expect("every legal group has an outcome");
                groups.insert(
                    (
                        self.obligations[obligation],
                        tuple.iter().map(|k| self.constants[k]).collect(),
                    ),
                    Self::status(&status),
                );
            }
        }
        Outcomes {
            groups,
            regions: r
                .regions
                .iter()
                .map(|(key, r)| {
                    (
                        self.region(key),
                        (
                            Self::status(&r.outcome),
                            match &r.completion {
                                RegionCompletion::NoContradiction => Completion::Clear,
                                RegionCompletion::NoMeaning { .. } => Completion::NoMeaning,
                                RegionCompletion::Deferred(_) => Completion::Deferred,
                                RegionCompletion::Inconclusive(r) => {
                                    Completion::Inconclusive(r.clone())
                                }
                            },
                        ),
                    )
                })
                .collect(),
            incomplete: r.incomplete.keys().map(|k| self.region(k)).collect(),
            unfinished: r.unfinished.clone(),
        }
    }
}
fn check(
    c: &Corpus,
    keys: &SemanticKeys,
    domains: &Domains,
    w: &[InputAtMostOne],
    backend: BackendIdentity,
    session: &mut Session,
    index: &Index,
) -> Outcomes {
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
    let mut request = CheckRequest::all_obligations(c, keys, domains, w, &limits).unwrap();
    request.backend = backend;
    let prepared = match session.prepare(&request, c, keys, &operations).unwrap() {
        RequestPreparation::Complete(p) => p,
        RequestPreparation::Inconclusive { reason, .. } => {
            return index.outcomes(&request.exhausted(reason));
        }
    };
    let prepared = prepared.admit(&operations).unwrap();
    let report = match session.verify(&prepared, &operations).unwrap() {
        LocalCheckOutcome::Complete(r) => r,
        LocalCheckOutcome::Inconclusive { reason, .. } => {
            return index.outcomes(&request.exhausted(reason));
        }
    };
    // verify() uses backend-specific concrete replay/certification before it can
    // produce CertifiedCandidate. Recheck overlap tuples in the ground program;
    // never pass SAT's separate unfounded-support world off as an overlap.
    for group in &report.checked.verification.groups {
        if let VerifiedOutcome::Counterexample(counterexample) = &group.outcome {
            assert!(counterexample.tuples.len() >= 2);
            let replay = prepared
                .program()
                .evaluate(counterexample.observation.present.iter().cloned(), &limits)
                .unwrap();
            for tuple in &counterexample.tuples {
                if !matches!(replay.fact(tuple).unwrap(), FactState::Settled(true)) {
                    let CertificationOutcome::Certified(certified) = prepared
                        .program()
                        .certify_observation(
                            counterexample.observation.present.iter().cloned(),
                            &limits,
                        )
                        .unwrap()
                    else {
                        panic!("counterexample failed replay/certification")
                    };
                    assert!(certified.facts.contains(tuple));
                }
            }
        }
    }
    index.outcomes(&report.checked.results.value)
}
fn gate(id: &str, program: LoweredProgram, sources: Sources) {
    eprintln!("round-trip {id}");
    let paths = sources
        .snapshots()
        .enumerate()
        .map(|(i, s)| (s.id, format!("sources/{i}.den")))
        .collect();
    let layout = export::layout(&program, &sources, &paths).unwrap();
    let assumptions = export::assumptions(&program);
    let domains = program.domains();
    let export = ExportProgram {
        corpus: &program.corpus,
        domains: &domains,
        sources: &sources,
        provenance: &program.attribution.provenance,
        assumptions: &assumptions,
        layout: &layout,
    };
    let bundle = print(&export, PrintOptions::default()).unwrap();
    if id == "multi-file/integers" {
        assert_eq!(assumptions.len(), 1);
        assert!(bundle.files["shared.den"].contains("const 1:"));
        assert!(bundle.files["shared.den"].contains("const 2:"));
        assert_eq!(program.corpus.sorts().count(), 3);
    }
    let (membership, documents) = bundle.documents("file:///export");
    let mut editor = denotate_ir_text::index::Index::default();
    for source in &documents {
        let tree = denotate_ir_text::parser()
            .parse(source.text.as_ref(), None)
            .unwrap();
        editor.update(source.clone(), tree);
    }
    editor.set_membership(&membership).unwrap();
    for source in &documents {
        let errors = editor
            .diagnostics(&membership.root, &source.uri)
            .into_iter()
            .filter(|d| !d.warning)
            .collect::<Vec<_>>();
        assert!(
            errors.is_empty(),
            "{id}: exported editor resolution: {errors:?}"
        );
    }

    let loaded = load_with_resolver(&membership, &documents, Some(&mut &sources))
        .unwrap_or_else(|e| panic!("{id}: {e:?}\n{:?}", bundle.files));
    assert!(loaded.embedded.notices.is_empty());
    let map = correspondence::compare(&export, &loaded, "file:///export", true);
    let left = Index::new(&program.corpus, &program.corpus, &program.keys, None);
    let right = Index::new(&program.corpus, &loaded.corpus, &loaded.keys, Some(&map));
    let w = assumptions
        .iter()
        .map(|a| a.constraint.clone())
        .collect::<Vec<_>>();
    let loaded_w = loaded
        .assumptions
        .iter()
        .map(|a| a.constraint.clone())
        .collect::<Vec<_>>();
    let mut previous: Option<Outcomes> = None;
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        let mut direct_session = Session::default();
        let mut text_session = Session::default();
        let direct = check(
            &program.corpus,
            &program.keys,
            &domains,
            &w,
            backend.clone(),
            &mut direct_session,
            &left,
        );
        let text = check(
            &loaded.corpus,
            &loaded.keys,
            &loaded.domains,
            &loaded_w,
            backend.clone(),
            &mut text_session,
            &right,
        );
        assert_eq!(
            direct, text,
            "{id}: direct versus text, {}",
            backend.backend
        );
        assert_eq!(
            direct,
            check(
                &program.corpus,
                &program.keys,
                &domains,
                &w,
                backend.clone(),
                &mut direct_session,
                &left
            ),
            "{id}: direct cold/warm"
        );
        assert_eq!(
            text,
            check(
                &loaded.corpus,
                &loaded.keys,
                &loaded.domains,
                &loaded_w,
                backend,
                &mut text_session,
                &right
            ),
            "{id}: text cold/warm"
        );
        if let Some(previous) = &previous {
            for (key, value) in &direct.groups {
                if let Some(other) = previous.groups.get(key) {
                    if matches!(value, Status::Proved | Status::Counterexample)
                        && matches!(other, Status::Proved | Status::Counterexample)
                    {
                        assert_eq!(value, other, "{id}: conclusive backend answers");
                    }
                }
            }
        }
        if let Some(previous) = &previous {
            for (key, (_, completion)) in &direct.regions {
                if let Some((_, other)) = previous.regions.get(key) {
                    if matches!(completion, Completion::Clear | Completion::NoMeaning)
                        && matches!(other, Completion::Clear | Completion::NoMeaning)
                    {
                        assert_eq!(completion, other, "{id}: conclusive region completion");
                    }
                }
            }
        }
        previous = Some(direct);
    }
}
#[test]
fn named_128_program_gate() {
    let mut count = 0;
    for (id, fixture) in [
        ("api/overlap", support::Fixture::overlap()),
        ("api/mixed", support::Fixture::mixed(false, false)),
        ("api/requires-c", support::Fixture::mixed(true, false)),
        ("api/fixed", support::Fixture::mixed(true, true)),
        ("api/exclusive", support::Fixture::exclusive()),
        ("api/ambiguous", support::Fixture::ambiguous()),
        ("api/redundant", support::Fixture::redundant()),
    ] {
        let LoweringOutcome::Lowered(p) = lowering::lower(&fixture.ast, &fixture.sources).unwrap()
        else {
            panic!("{id}")
        };
        gate(id, p, fixture.sources);
        count += 1;
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut cases = vec![];
    for (id, path) in [
        ("text/overlap", "fixtures/overlapping-mappings.txt"),
        (
            "text/vscode-overlap",
            "vscode/examples/overlap.inputmapping",
        ),
        ("text/vscode-values", "vscode/examples/values.inputmapping"),
    ] {
        cases.push((
            id.into(),
            vec![SourceFile::new(
                format!("file:///{id}.inputmapping"),
                1,
                std::fs::read_to_string(root.join(path)).unwrap(),
            )],
        ));
    }
    let pre: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("fixtures/pre-normalize.json")).unwrap(),
    )
    .unwrap();
    let indices = (0..=13).chain(17..=31).chain(35..=37).collect::<Vec<_>>();
    assert_eq!(indices.len(), 32);
    for i in indices {
        cases.push((
            format!("pre-normalize/{i:02}"),
            vec![SourceFile::new(
                "file:///case.inputmapping",
                1,
                pre["cases"][i]["text"].as_str().unwrap(),
            )],
        ));
    }
    let captured: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("fixtures/pre-integration-fingerprints.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(captured["cases"].as_array().unwrap().len(), 84);
    for i in 0..84 {
        let case = &captured["cases"][i];
        cases.push((
            format!("pre-integration/{i:02}"),
            vec![SourceFile::new(
                "file:///case.inputmapping",
                case["revision"].as_u64().unwrap(),
                case["text"].as_str().unwrap(),
            )],
        ));
    }
    cases.push((
        "multi-file/overlap".into(),
        vec![
            SourceFile::new(
                "file:///declarations.inputmapping",
                1,
                "input i, j; slot a;",
            ),
            SourceFile::new("file:///left.inputmapping", 1, "a <- i;"),
            SourceFile::new("file:///right.inputmapping", 1, "a <- j;"),
        ],
    ));
    cases.push((
        "multi-file/integers".into(),
        vec![
            SourceFile::new(
                "file:///a.inputmapping",
                1,
                "input i; slot a; a <- i when input_value(i) is 1;",
            ),
            SourceFile::new(
                "file:///b.inputmapping",
                1,
                "input j; slot b; b <- j when input_value(j) is 2;",
            ),
        ],
    ));
    assert_eq!(cases.len() + count, 128);
    for (id, docs) in cases {
        let assembled = export::assemble(&docs).unwrap_or_else(|e| panic!("{id}: {e:?}"));
        gate(&id, assembled.program, assembled.sources);
        count += 1;
    }
    assert_eq!(count, 128);
}
#[test]
fn named_rejections_and_combined_file_contract() {
    let pre: serde_json::Value =
        serde_json::from_str(include_str!("../fixtures/pre-normalize.json")).unwrap();
    for i in [14, 15, 16, 32, 33, 34] {
        let text = pre["cases"][i]["text"].as_str().unwrap();
        let errors = export::assemble(&[SourceFile::new("file:///bad", 1, text)])
            .err()
            .unwrap();
        assert!(!errors.is_empty(), "pre-normalize/{i}");
        if i < 17 {
            assert!(
                errors
                    .iter()
                    .any(|e| e.message.contains("Name") || e.message.contains("Kind")),
                "{errors:?}"
            );
        } else {
            assert!(
                errors.iter().all(
                    |e| e.message == "Unexpected syntax." || e.message.starts_with("Expected ")
                ),
                "{errors:?}"
            );
        }
    }
    assert!(
        export::assemble(&[SourceFile::new(
            "file:///lowering",
            1,
            include_str!("../fixtures/lowering.txt")
        )])
        .is_err()
    );
    let a = SourceFile::new("file:///a", 1, "input i; slot a; a <- i;");
    let b = SourceFile::new("file:///b", 1, "input j; a <- j;");
    assert!(export::assemble(&[a.clone(), a.clone()]).is_err());
    assert!(
        export::assemble(&[
            a.clone(),
            SourceFile::new("file:///duplicate", 1, "input i;")
        ])
        .is_err()
    );
    let export_docs = |docs: &[SourceFile]| {
        let a = export::assemble(docs).unwrap();
        let paths = a
            .sources
            .snapshots()
            .enumerate()
            .map(|(i, s)| (s.id, format!("sources/{i}.den")))
            .collect();
        export::bundle(&a.program, &a.sources, &paths, PrintOptions::default()).unwrap()
    };
    assert_eq!(export_docs(&[a.clone(), b.clone()]), export_docs(&[b, a]));
}

#[test]
fn warm_lowering_and_fresh_assemblies_export_identical_bytes() {
    let f = support::Fixture::overlap();
    let mut session = lowering::incremental::Session::new(true);
    let render = |p: LoweredProgram| {
        let paths = f
            .sources
            .snapshots()
            .map(|s| (s.id, "sources/program.den".into()))
            .collect();
        export::bundle(&p, &f.sources, &paths, PrintOptions::default()).unwrap()
    };
    let LoweringOutcome::Lowered(cold) = session.lower(&f.ast, &f.sources).unwrap() else {
        panic!()
    };
    let LoweringOutcome::Lowered(warm) = session.lower(&f.ast, &f.sources).unwrap() else {
        panic!()
    };
    let LoweringOutcome::Lowered(fresh) = lowering::lower(&f.ast, &f.sources).unwrap() else {
        panic!()
    };
    assert_eq!(render(cold), render(warm));
    assert_eq!(render(fresh), render(f.lower()));
}

#[test]
fn narrowed_domains_and_active_assumptions_change_both_paths_together() {
    for (domain, assumption, expected) in [
        ("", "", Status::Counterexample),
        (
            "",
            "assumption w: at_most_one(p, group_by: ());",
            Status::Proved,
        ),
        ("domain S = [a];", "", Status::Proved),
        ("domain S = [];", "", Status::Proved),
    ] {
        let doc = SourceFile::new(
            "file:///original.den",
            1,
            format!(
                "sort S; const a, b: S; input p(x: S); relation q(x: S); q(X) :- p(X); obligation unique: at_most_one(q, group_by: ()); {domain} {assumption}"
            ),
        );
        let p = load(
            &ProgramMembership::single("root", [doc.uri.clone()]),
            &[doc],
        )
        .unwrap();
        let assumptions = p
            .assumptions
            .iter()
            .map(|a| ExportAssumption {
                namespace: a.namespace.clone(),
                name: Some(a.name.name.to_string()),
                constraint: a.constraint.clone(),
                origins: vec![Origin::new(a.location)],
            })
            .collect::<Vec<_>>();
        let layout = ExportLayout {
            files: vec![ExportFile {
                path: "program.den".into(),
                ownership: Ownership::User,
            }],
            placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
            assumptions: vec![0; assumptions.len()],
        };
        let export = ExportProgram {
            corpus: &p.corpus,
            domains: &p.domains,
            sources: &p.sources,
            provenance: &p.provenance,
            assumptions: &assumptions,
            layout: &layout,
        };
        let (membership, docs) = print(&export, PrintOptions::default())
            .unwrap()
            .documents("file:///export");
        let q = load_with_resolver(&membership, &docs, Some(&mut &p.sources)).unwrap();
        let map = correspondence::compare(&export, &q, "file:///export", true);
        for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
            for (current, index) in [
                (&p, Index::new(&p.corpus, &p.corpus, &p.keys, None)),
                (&q, Index::new(&p.corpus, &q.corpus, &q.keys, Some(&map))),
            ] {
                let w = current
                    .assumptions
                    .iter()
                    .map(|a| a.constraint.clone())
                    .collect::<Vec<_>>();
                let actual = check(
                    &current.corpus,
                    &current.keys,
                    &current.domains,
                    &w,
                    backend.clone(),
                    &mut Session::default(),
                    &index,
                );
                assert_eq!(actual.groups.values().collect::<Vec<_>>(), vec![&expected]);
            }
        }
    }
}

#[test]
fn unambiguous_witness_keeps_exact_primary_and_related_generic_origins() {
    use denotate_ir_text::origins::OriginDescriptor;
    let text = "input i, j; slot a; a <- i; a <- j;";
    let a = export::assemble(&[SourceFile::new("file:///witness.inputmapping", 1, text)]).unwrap();
    let paths = a
        .sources
        .snapshots()
        .map(|s| (s.id, "source.den".into()))
        .collect();
    let bundle = export::bundle(&a.program, &a.sources, &paths, PrintOptions::default()).unwrap();
    let (membership, docs) = bundle.documents("file:///export");
    let q = load_with_resolver(&membership, &docs, Some(&mut &a.sources)).unwrap();
    let snapshot = a.sources.snapshots().next().unwrap().id;
    let expected = [("a <- i", "i"), ("a <- j", "j")]
        .map(|(mapping, _)| {
            let start = text.find(mapping).unwrap();
            [start..start + 1, start + 5..start + 6].map(|range| {
                OriginDescriptor::of(
                    &a.sources,
                    &Origin::new(a.sources.span(snapshot, range).unwrap()),
                )
                .unwrap()
            })
        })
        .into_iter()
        .collect::<BTreeSet<_>>();
    let domains = a.program.domains();
    let w = export::assumptions(&a.program)
        .into_iter()
        .map(|a| a.constraint)
        .collect::<Vec<_>>();
    let qw = q
        .assumptions
        .iter()
        .map(|a| a.constraint.clone())
        .collect::<Vec<_>>();
    for backend in [BackendIdentity::bdd(), BackendIdentity::sat()] {
        for (c, keys, domains, w, sources, provenance) in [
            (
                &a.program.corpus,
                &a.program.keys,
                &domains,
                &w,
                &a.sources,
                &a.program.attribution.provenance,
            ),
            (
                &q.corpus,
                &q.keys,
                &q.domains,
                &qw,
                &q.sources,
                &q.embedded.provenance,
            ),
        ] {
            let limits = Limits::default();
            let operations = OperationalLimits::from(&limits);
            let mut request = CheckRequest::all_obligations(c, keys, domains, w, &limits).unwrap();
            request.backend = backend.clone();
            let mut session = Session::default();
            let RequestPreparation::Complete(prepared) =
                session.prepare(&request, c, keys, &operations).unwrap()
            else {
                panic!()
            };
            let prepared = prepared.admit(&operations).unwrap();
            let LocalCheckOutcome::Complete(report) =
                session.verify(&prepared, &operations).unwrap()
            else {
                panic!()
            };
            let mut actual = BTreeSet::new();
            for group in &report.checked.verification.groups {
                if let VerifiedOutcome::Counterexample(example) = &group.outcome {
                    for step in example.evidence.values() {
                        if let GroundEvidence::Derived { rule, .. } = &step.evidence {
                            if c.relation(rule.head.atom.relation).unwrap().name == "mapped_to" {
                                actual.insert([1, 0].map(|index| {
                                    let origins = provenance.origins(rule.head.arguments[index]);
                                    assert_eq!(origins.len(), 1);
                                    OriginDescriptor::of(sources, &origins[0]).unwrap()
                                }));
                            }
                        }
                    }
                }
            }
            assert_eq!(actual, expected);
        }
    }
}
