//! Run while both production paths exist, then retain via the pre-deletion commit.
#[path = "support/normalization_cases.rs"]
mod cases;
#[path = "support/normalization_fingerprint.rs"]
mod fingerprint;
use denotate_editor::Document;
use denotate_ir::Sources;
use denotate_test_dsl::{
    lowering::{self, assembly, projection, recipe, semantic, shared},
    syntax,
};
use serde_json::{Value, json};
use std::time::Instant;
fn parse(text: &str, revision: u64) -> (denotate_test_dsl::ast::Program, Sources) {
    let mut sources = Sources::new();
    let snapshot = sources
        .add("file:///generic.inputmapping", revision, "test-dsl", text)
        .unwrap();
    let doc = Document::new(
        &mut syntax::parser().unwrap(),
        text.into(),
        revision as i32,
        true,
    );
    let syntax::ParseOutcome::Parsed(ast) = syntax::project(&doc, &sources, snapshot).unwrap()
    else {
        panic!("syntax")
    };
    (ast, sources)
}
fn lower(text: &str, revision: u64) -> Value {
    let (ast, sources) = parse(text, revision);
    let lowering::LoweringOutcome::Lowered(p) = lowering::lower(&ast, &sources).unwrap() else {
        panic!("names")
    };
    fingerprint::fingerprint(&p, &sources)
}
#[test]
#[ignore = "capture on the legacy implementation only; never refresh expectations"]
fn capture_additional_legacy_fingerprints() {
    let cases:Vec<_>=cases::capture_cases().into_iter().map(|(revision,text)|json!({"revision":revision,"fingerprint":lower(&text,revision),"text":text})).collect();
    assert_eq!(cases.len(), 84);
    println!(
        "LEGACY_FINGERPRINTS={}",
        json!({"production_revision":"ef11c66", "cases":cases})
    );
}
#[test]
#[ignore = "paired release assembly measurement; no CI timing gate"]
fn measure_paired_assembly() {
    assert!(!cfg!(debug_assertions), "run with --release");
    let mut rows = vec![];
    for size in [10, 100, 1000] {
        let slots = (0..size)
            .map(|i| format!("s{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let mappings = (0..size)
            .map(|i| format!("s{i} <- i when (present(i) or present(j)) and present(i);\n"))
            .collect::<String>();
        let text = format!("input i, j;\nslot {slots};\n{mappings}");
        let (ast, sources) = parse(&text, 1);
        let projection = projection::project(&ast, &sources).unwrap();
        let keys = projection.keys();
        assert!(semantic::validate(&keys).unwrap().is_empty());
        let old = keys
            .iter()
            .map(|s| recipe::Recipe::lower(s.form.clone()))
            .collect::<Vec<_>>();
        let new = keys
            .iter()
            .map(|s| shared::Recipe::lower(s.form.clone()).unwrap())
            .collect::<Vec<_>>();
        let legacy = || {
            let start = Instant::now();
            let p = assembly::assemble(&projection, &old, &sources).unwrap();
            (start.elapsed().as_nanos(), p)
        };
        let candidate = || {
            let start = Instant::now();
            let p = shared::assemble(&projection, &new, &sources).unwrap();
            (start.elapsed().as_nanos(), p)
        };
        let mut samples = vec![];
        for pair in 0..35 {
            let ((old_ns, old_p), (new_ns, new_p)) = if pair % 2 == 0 {
                (legacy(), candidate())
            } else {
                let new = candidate();
                (legacy(), new)
            };
            assert_eq!(
                fingerprint::fingerprint(&old_p, &sources),
                fingerprint::fingerprint(&new_p, &sources)
            );
            if pair >= 5 {
                samples.push(json!({"legacy_ns":old_ns,"candidate_ns":new_ns,"first":if pair%2==0 {"legacy"} else {"candidate"}}));
            }
        }
        rows.push(json!({"mappings":size,"helpers":size,"inputs":2,"source":text,"warmup_pairs":5,"measured_pairs":30,"samples":samples}));
    }
    println!(
        "PAIRED_ASSEMBLY={}",
        json!({"rows":rows,"timed_boundary":"Fresh assembly and attribution only; parsing, validation, recipe creation, fingerprints, checking and program destruction excluded. Equivalent precomputed recipes, identical projection and sources, five warm-up pairs and 30 alternating measured pairs per size."})
    );
}
