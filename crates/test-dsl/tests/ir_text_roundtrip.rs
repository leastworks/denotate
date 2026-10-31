#[path = "support/corpus.rs"]
mod corpus;
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
fn default_request(p: &LoadedProgram, limits: &Limits) -> CheckRequest {
    let mut requests = p.verification_requests(limits).unwrap();
    assert_eq!(requests.len(), 1);
    let (key, request) = requests.pop().unwrap();
    assert_eq!(request.verification.as_ref(), Some(&key));
    request
}
fn check(
    c: &Corpus,
    keys: &SemanticKeys,
    request: &CheckRequest,
    session: &mut Session,
    index: &Index,
) -> Outcomes {
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
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
    // verify() uses concrete replay/certification before it can
    // produce CertifiedCandidate. Recheck overlap tuples in the ground program;
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
    let domains = program.domains();
    let export = ExportProgram {
        corpus: &program.corpus,
        domains: &domains,
        sources: &sources,
        provenance: &program.attribution.provenance,
        layout: &layout,
    };
    let bundle = print(&export, PrintOptions::default()).unwrap();
    if id == "multi-file/integers" {
        assert_eq!(program.corpus.assumptions().count(), 1);
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
    let verification = loaded.corpus.verifications().next().unwrap();
    assert_eq!(loaded.corpus.verifications().count(), 1);
    assert_eq!(
        map.ids[&program.library.default_checks.into()],
        verification.id.into()
    );
    assert_eq!(verification.assumptions.len(), 1);
    assert_eq!(
        map.ids[&program.library.one_value_per_input.into()],
        verification.assumptions[0].into()
    );
    assert_eq!(verification.obligations.len(), 1);
    assert_eq!(
        map.ids[&program.library.unique_input.into()],
        verification.obligations[0].into()
    );
    assert!(bundle.files["library/library.den"].contains("verification default_checks"));
    if !id.starts_with("api/") && !id.starts_with("multi-file/") {
        presentation_gate(id, &program, &sources, &loaded, &left, &right);
    }
    {
        let mut direct_session = Session::default();
        let mut text_session = Session::default();
        let direct_request = program.request(&Limits::default()).unwrap();
        let text_request = default_request(&loaded, &Limits::default());
        assert_eq!(
            direct_request.obligations,
            BTreeSet::from([program
                .keys
                .obligation(program.library.unique_input)
                .unwrap()
                .clone()])
        );
        assert_eq!(
            text_request.obligations,
            BTreeSet::from([loaded
                .keys
                .obligation(verification.obligations[0])
                .unwrap()
                .clone()])
        );
        assert_eq!(
            direct_request.verification,
            Some(
                program
                    .keys
                    .verification(program.library.default_checks)
                    .unwrap()
                    .clone()
            )
        );
        assert_eq!(
            text_request.verification,
            Some(loaded.keys.verification(verification.id).unwrap().clone())
        );
        let direct = check(
            &program.corpus,
            &program.keys,
            &direct_request,
            &mut direct_session,
            &left,
        );
        let text = check(
            &loaded.corpus,
            &loaded.keys,
            &text_request,
            &mut text_session,
            &right,
        );
        assert_eq!(direct, text, "{id}: direct versus text");
        assert_eq!(
            direct,
            check(
                &program.corpus,
                &program.keys,
                &direct_request,
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
                &text_request,
                &mut text_session,
                &right
            ),
            "{id}: text cold/warm"
        );
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
            "../../editors/test-dsl/examples/overlap.testdsl",
        ),
        (
            "text/vscode-values",
            "../../editors/test-dsl/examples/values.testdsl",
        ),
    ] {
        cases.push((
            id.into(),
            vec![SourceFile::new(
                format!("file:///{id}.testdsl"),
                1,
                std::fs::read_to_string(root.join(path)).unwrap(),
            )],
        ));
    }
    assert_eq!(corpus::programs().len(), 39);
    let accepted = corpus::accepted();
    assert_eq!(accepted.len(), 33);
    for (i, text) in accepted {
        cases.push((
            format!("corpus/{i:02}"),
            vec![SourceFile::new("file:///case.testdsl", 1, text)],
        ));
    }
    let generated = corpus::generated();
    assert_eq!(generated.len(), 84);
    for (i, (revision, text)) in generated.into_iter().enumerate() {
        cases.push((
            format!("generated/{i:02}"),
            vec![SourceFile::new("file:///case.testdsl", revision, text)],
        ));
    }
    // Named parser-backed single-file parity catalog. Never filter failures.
    assert_eq!(cases.len(), 120);
    cases.push((
        "multi-file/overlap".into(),
        vec![
            SourceFile::new("file:///declarations.testdsl", 1, "input i, j; slot a;"),
            SourceFile::new("file:///left.testdsl", 1, "a <- i;"),
            SourceFile::new("file:///right.testdsl", 1, "a <- j;"),
        ],
    ));
    cases.push((
        "multi-file/integers".into(),
        vec![
            SourceFile::new(
                "file:///a.testdsl",
                1,
                "input i; slot a; a <- i when input_value(i) is 1;",
            ),
            SourceFile::new(
                "file:///b.testdsl",
                1,
                "input j; slot b; b <- j when input_value(j) is 2;",
            ),
        ],
    ));
    assert_eq!(cases.len() + count, 129);
    for (id, docs) in cases {
        let assembled = export::assemble(&docs).unwrap_or_else(|e| panic!("{id}: {e:?}"));
        gate(&id, assembled.program, assembled.sources);
        count += 1;
    }
    assert_eq!(count, 129);
}
#[test]
fn named_rejections_and_combined_file_contract() {
    let programs = corpus::programs();
    for i in corpus::REJECTED {
        let text = programs[i];
        let errors = export::assemble(&[SourceFile::new("file:///bad", 1, text)])
            .err()
            .unwrap();
        assert!(!errors.is_empty(), "corpus/{i}");
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
                "sort S; const a, b: S; input p(x: S); relation q(x: S); q(X) :- p(X); obligation unique: at_most_one(q, group_by: ()); {domain} {assumption} verification checks {{ assumptions: [{selected}]; obligations: [unique]; }}",
                selected = if assumption.is_empty() { "" } else { "w" }
            ),
        );
        let p = load(
            &ProgramMembership::single("root", [doc.uri.clone()]),
            &[doc],
        )
        .unwrap();
        let layout = ExportLayout {
            files: vec![ExportFile {
                path: "program.den".into(),
                ownership: Ownership::User,
            }],
            placements: top_level(&p.corpus).into_iter().map(|id| (id, 0)).collect(),
        };
        let export = ExportProgram {
            corpus: &p.corpus,
            domains: &p.domains,
            sources: &p.sources,
            provenance: &p.provenance,
            layout: &layout,
        };
        let (membership, docs) = print(&export, PrintOptions::default())
            .unwrap()
            .documents("file:///export");
        let q = load_with_resolver(&membership, &docs, Some(&mut &p.sources)).unwrap();
        let map = correspondence::compare(&export, &q, "file:///export", true);
        {
            for (current, index) in [
                (&p, Index::new(&p.corpus, &p.corpus, &p.keys, None)),
                (&q, Index::new(&p.corpus, &q.corpus, &q.keys, Some(&map))),
            ] {
                let actual = check(
                    &current.corpus,
                    &current.keys,
                    &default_request(current, &Limits::default()),
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
    let a = export::assemble(&[SourceFile::new("file:///witness.testdsl", 1, text)]).unwrap();
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
    {
        for (c, keys, request, sources, provenance) in [
            (
                &a.program.corpus,
                &a.program.keys,
                a.program.request(&Limits::default()).unwrap(),
                &a.sources,
                &a.program.attribution.provenance,
            ),
            (
                &q.corpus,
                &q.keys,
                default_request(&q, &Limits::default()),
                &q.sources,
                &q.embedded.provenance,
            ),
        ] {
            let limits = Limits::default();
            let operations = OperationalLimits::from(&limits);
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum FindingIdentity {
    Coverage(usize),
    Emptiness(usize),
    Group(usize, Vec<usize>),
    Uniqueness(usize, Vec<usize>),
    Region(Vec<AtomIdentity>),
}
fn finding_identity(
    index: &Index,
    keys: &SemanticKeys,
    id: &denotate_presentation::Identity,
) -> FindingIdentity {
    use denotate_presentation::Identity;
    match id {
        Identity::InconsistentAssumptions | Identity::AssumedConclusion(..) => panic!(
            "test DSL input-cardinality contracts are consistent and do not assume their conclusion"
        ),
        Identity::Emptiness(id) => {
            FindingIdentity::Emptiness(index.obligations[keys.obligation(*id).unwrap()])
        }
        Identity::Coverage(id) => {
            FindingIdentity::Coverage(index.obligations[keys.obligation(*id).unwrap()])
        }
        Identity::Group { obligation, tuple } => FindingIdentity::Group(
            index.obligations[keys.obligation(*obligation).unwrap()],
            tuple
                .iter()
                .map(|c| index.constants[keys.constant(*c).unwrap()])
                .collect(),
        ),
        Identity::Uniqueness { obligation, tuple } => FindingIdentity::Uniqueness(
            index.obligations[keys.obligation(*obligation).unwrap()],
            tuple
                .iter()
                .map(|c| index.constants[keys.constant(*c).unwrap()])
                .collect(),
        ),
        Identity::Region(atoms) => {
            let mut atoms = atoms
                .iter()
                .map(|a| index.atom(&AtomKey::from_atom(keys, a).unwrap()))
                .collect::<Vec<_>>();
            atoms.sort();
            FindingIdentity::Region(atoms)
        }
        Identity::Rewrite { .. } => {
            panic!("rewrite is tested separately from semantic finding parity")
        }
    }
}
/// Presenter boundary gate; actual B publications await stage 4. No wording or
/// diagnostic-count comparison: each frontend may highlight several occurrences.
fn presentation_gate(
    id: &str,
    p: &LoweredProgram,
    sources: &Sources,
    q: &LoadedProgram,
    left: &Index,
    right: &Index,
) {
    use denotate_presentation::Kind;
    use denotate_test_dsl::presentation as dsl;
    let limits = Limits::default();
    let ops = OperationalLimits::from(&limits);
    {
        let mut direct_session = Session::default();
        let mut text_session = Session::default();
        let mut previous = None;
        for _ in 0..2 {
            let request = p.request(&limits).unwrap();
            let RequestPreparation::Complete(prepared) = direct_session
                .prepare(&request, &p.corpus, &p.keys, &ops)
                .unwrap()
            else {
                panic!("{id}: direct preparation incomplete")
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(direct) =
                direct_session.verify(&prepared, &ops).unwrap()
            else {
                panic!("{id}: direct checking incomplete")
            };
            let findings = dsl::present_checked(p, &direct.checked, sources, "test-dsl")
                .unwrap_or_else(|e| panic!("{id}: {e}"));
            let direct_set = findings
                .iter()
                .map(|f| {
                    (
                        f.kind.semantic_kind(),
                        finding_identity(left, &p.keys, &f.identity),
                    )
                })
                .collect::<BTreeSet<_>>();
            let request = default_request(q, &limits);
            let RequestPreparation::Complete(prepared) = text_session
                .prepare(&request, &q.corpus, &q.keys, &ops)
                .unwrap()
            else {
                panic!("{id}: text preparation incomplete")
            };
            let prepared = prepared.admit(&ops).unwrap();
            let LocalCheckOutcome::Complete(text) = text_session.verify(&prepared, &ops).unwrap()
            else {
                panic!("{id}: text checking incomplete")
            };
            let output = denotate_ir_text::presentation::present(q, &text.checked).unwrap();
            let text_set = output
                .diagnostics
                .iter()
                .filter(|d| d.kind != Kind::Rewrite)
                .map(|d| (d.kind, finding_identity(right, &q.keys, &d.identity)))
                .collect::<BTreeSet<_>>();
            assert_eq!(direct_set, text_set, "{id}: presenter parity");
            if let Some(previous) = &previous {
                assert_eq!(previous, &direct_set, "{id}: presenter cold/warm");
            }
            previous = Some(direct_set);
            // Both sides expose their own replayed witness; generic origins come
            // from its producing occurrences, not a second solver's chosen path.
            for d in &output.diagnostics {
                if d.kind == Kind::Counterexample {
                    assert_eq!(d.evidence["kind"], "replayed-counterexample");
                    assert!(d.evidence["tuples"].as_array().unwrap().len() >= 2);
                    assert!(!d.evidence["producers"].as_array().unwrap().is_empty());
                }
            }
            if id == "text/unambiguous-presentation" {
                use denotate_ir_text::origins::OriginDescriptor;
                let expected = findings
                    .iter()
                    .filter(|d| d.kind == dsl::DiagnosticKind::OverlappingMappings)
                    .map(|d| OriginDescriptor::of(sources, &Origin::new(d.primary)).unwrap())
                    .collect::<BTreeSet<_>>();
                assert_eq!(expected.len(), 2);
                let actual = output
                    .diagnostics
                    .iter()
                    .filter(|d| d.kind == Kind::Counterexample)
                    .flat_map(|d| &d.related)
                    .map(|r| OriginDescriptor::of(&q.sources, &Origin::new(r.span)).unwrap())
                    .collect::<BTreeSet<_>>();
                assert!(
                    expected.is_subset(&actual),
                    "every highlighted DSL span must be related in .den"
                );
                for d in output
                    .diagnostics
                    .iter()
                    .filter(|d| d.kind == Kind::Counterexample)
                {
                    assert!(q.sources.text(d.primary).unwrap().contains("mapped_to"));
                    assert!(!d.fallback);
                }
            }
        }
    }
}

#[test]
fn unambiguous_presenters_preserve_every_primary_dsl_span() {
    let assembled = export::assemble(&[SourceFile::new(
        "file:///witness.testdsl",
        1,
        "input i, j; slot a; a <- i; a <- j;",
    )])
    .unwrap();
    gate(
        "text/unambiguous-presentation",
        assembled.program,
        assembled.sources,
    );
}
