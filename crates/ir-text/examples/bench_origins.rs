//! Synthetic origin-loading measurements, not a timing gate or production scorecard.
use denotate_check::{Limits, LocalCheckOutcome, OperationalLimits, RequestPreparation};
use denotate_check_session::Session;
use denotate_ir_text::{filesystem, load_with_resolver, origins::content_hash};
use std::{fmt::Write, fs, path::PathBuf, time::Instant};

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let files: usize = args
        .next()
        .expect("FILES [ITEMS=100] [PADDING=0] [--long-line]")
        .parse()
        .unwrap();
    let items: usize = args.next().unwrap_or("100".into()).parse().unwrap();
    let padding: usize = args.next().unwrap_or("0".into()).parse().unwrap();
    let long_line = match args.next().as_deref() {
        None => false,
        Some("--long-line") => true,
        Some(other) => panic!("unexpected argument {other}"),
    };
    assert!(args.next().is_none());
    assert!(files > 0 && items > 0, "FILES and ITEMS must be positive");
    let root = std::env::temp_dir().join(format!("denotate-origin-bench-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let scratch = Scratch(root.canonicalize().unwrap());
    let source_dir = scratch.0.join("sources");
    fs::create_dir(&source_dir).unwrap();
    let program = scratch.0.join("program");
    fs::create_dir(&program).unwrap();
    fs::write(program.join("den.root"), "{}").unwrap();
    fs::write(program.join("checks.den"), "relation nothing(); obligation clean: empty(nothing); verification checks { assumptions: []; obligations: [clean]; }").unwrap();

    for mode in ["without", "unavailable", "resolved"] {
        for file in 0..files {
            // Keep the IR fixed while independently varying source length. Both
            // multiline and long-line inputs exercise Unicode-scalar coordinates.
            let prefix = "x".repeat(padding);
            let source = if long_line {
                format!("{prefix}{}", "é😀\r".repeat(items))
            } else {
                format!("{prefix}\n{}", "é😀\r\n".repeat(items))
            };
            let source_path = source_dir.join(format!("{file}.dsl"));
            fs::write(&source_path, &source).unwrap();
            let mut text = format!("namespace n{file} {{\n");
            let loc = |item: usize| {
                if mode == "without" {
                    String::new()
                } else if long_line {
                    let column = padding + item * 3 + 1;
                    format!(" loc(#s 1:{column} to 1:{})", column + 3)
                } else {
                    format!(" loc(#s {}:1 to {}:4)", item + 2, item + 2)
                }
            };
            writeln!(
                text,
                "sort S{}; relation p(x:S){}; relation q(x:S){};",
                loc(0),
                loc(0),
                loc(0)
            )
            .unwrap();
            for item in 0..items {
                let at = loc(item);
                writeln!(
                    text,
                    "const c{item}: S{at}; p(c{item}){at}; q(c{item}) :- p(c{item}){at};"
                )
                .unwrap();
            }
            text.push_str("}\n");
            if mode != "without" {
                writeln!(
                    text,
                    "#s = source({:?}, view: \"dsl\", hash: {:?});",
                    filesystem::uri(&source_path),
                    content_hash(&source)
                )
                .unwrap();
            }
            fs::write(program.join(format!("{file}.den")), text).unwrap();
        }
        let start = Instant::now();
        let (membership, documents) = filesystem::discover(&program).unwrap();
        let discovery = start.elapsed().as_secs_f64();
        let start = Instant::now();
        let mut resolver = filesystem::FileOriginResolver;
        let p = load_with_resolver(
            &membership,
            &documents,
            (mode == "resolved").then_some(&mut resolver),
        )
        .unwrap();
        let loading = start.elapsed().as_secs_f64();
        assert_eq!(
            p.embedded.notices.len(),
            if mode == "unavailable" { files } else { 0 }
        );
        let start = Instant::now();
        let limits = Limits::default();
        let ops = OperationalLimits::from(&limits);
        assert!(
            denotate_check::validate_assumption_cones(&p.corpus, &p.domains, &p.keys, &limits)
                .unwrap()
                .is_valid()
        );
        let (_, request) = p.verification_requests(&limits).unwrap().remove(0);
        let mut session = Session::default();
        let RequestPreparation::Complete(prepared) =
            session.prepare(&request, &p.corpus, &p.keys, &ops).unwrap()
        else {
            panic!("incomplete preparation")
        };
        let admitted = prepared.admit(&ops).unwrap();
        let LocalCheckOutcome::Complete(report) = session.verify(&admitted, &ops).unwrap() else {
            panic!("incomplete checking")
        };
        assert!(report.checked.verification.all_obligations_proved());
        let checking = start.elapsed().as_secs_f64();
        println!(
            "{}",
            serde_json::json!({
                "files": files, "itemsPerFile": items, "padding": padding,
                "longLine": long_line, "origins": mode,
                "denBytes": documents.iter().map(|d|d.text.len()).sum::<usize>(),
                "associations": p.embedded.associations.len(),
                "discoverySeconds": discovery, "loadingSeconds": loading,
                "checkingSeconds": checking, "outcome": "proved"
            })
        );
    }
}
