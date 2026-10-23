//! Load and check supplied .den modules. The LSP presenter is a later increment.
use denotate_check::{
    BackendIdentity, Limits, LocalCheckOutcome, OperationalLimits, RequestPreparation,
};
use denotate_check_session::Session;
use denotate_ir_text::{SourceFile, load};

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let root = args.next().ok_or("Usage: check ROOT FILE... [--sat]")?;
    let mut sources = Vec::new();
    let mut backend = BackendIdentity::bdd();
    for file in args {
        if file == "--sat" {
            backend = BackendIdentity::sat();
            continue;
        }
        let path = std::fs::canonicalize(&file).map_err(|e| format!("{file}: {e}"))?;
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{file}: {e}"))?;
        let escaped = path
            .to_string_lossy()
            .as_bytes()
            .iter()
            .map(|b| {
                if b.is_ascii_alphanumeric() || b"/._~-:".contains(b) {
                    (*b as char).to_string()
                } else {
                    format!("%{b:02X}")
                }
            })
            .collect::<String>();
        sources.push(SourceFile::new(format!("file://{escaped}"), 1, text));
    }
    let p = load(&root, &sources).map_err(|ds| {
        ds.iter()
            .map(|d| {
                format!(
                    "{}:{}..{}: {}",
                    d.uri, d.range.start, d.range.end, d.message
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    println!(
        "Root: {}. Backend: {}. Modules: {}.",
        p.root,
        backend.backend,
        p.modules.len()
    );
    if p.modules.iter().any(|m| !m.location_syntax.is_empty()) {
        println!("Provenance: .den only; embedded DSL origins are not restored yet.");
    }
    println!(
        "Active assumptions: {:?}",
        p.assumptions
            .iter()
            .map(|a| format!("{}::{}", a.name.namespace, a.name.name))
            .collect::<Vec<_>>()
    );
    let limits = Limits::default();
    let operations = OperationalLimits::from(&limits);
    let request = p.request(&limits, backend).map_err(|e| e.to_string())?;
    let mut session = Session::default();
    let prepared = session
        .prepare(&request, &p.corpus, &p.keys, &operations)
        .map_err(|e| e.to_string())?;
    let prepared = match prepared {
        RequestPreparation::Complete(prepared) => prepared,
        RequestPreparation::Inconclusive { reason, .. } => {
            println!("Inconclusive: {reason:?}");
            return Ok(());
        }
    };
    let admitted = prepared.admit(&operations).map_err(|e| e.to_string())?;
    match session
        .verify(&admitted, &operations)
        .map_err(|e| e.to_string())?
    {
        LocalCheckOutcome::Complete(report) => println!("{:#?}", report.checked.results.value),
        LocalCheckOutcome::Inconclusive { reason, .. } => println!("Inconclusive: {reason:?}"),
    }
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
