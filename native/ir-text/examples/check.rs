//! Load and check a den.root program. The LSP presenter is a later increment.
use denotate_check::{
    BackendIdentity, Limits, LocalCheckOutcome, OperationalLimits, RequestPreparation,
};
use denotate_check_session::Session;
use denotate_ir_text::{filesystem, load};

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let root = args
        .next()
        .ok_or("Usage: check ROOT_FOLDER_OR_DEN.ROOT [--sat]")?;
    let mut backend = BackendIdentity::bdd();
    for option in args {
        if option != "--sat" {
            return Err(format!(
                "Unknown argument {option:?}; usage: check ROOT_FOLDER_OR_DEN.ROOT [--sat]"
            ));
        }
        backend = BackendIdentity::sat();
    }
    let format_errors = |ds: Vec<denotate_ir_text::Diagnostic>| {
        ds.iter()
            .map(|d| {
                format!(
                    "{}:{}..{}: {}",
                    d.uri, d.range.start, d.range.end, d.message
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let (membership, sources) =
        filesystem::discover(std::path::Path::new(&root)).map_err(format_errors)?;
    let p = load(&membership, &sources).map_err(format_errors)?;
    println!(
        "Root: {}. Backend: {}. Files: {}.",
        p.root,
        backend.backend,
        p.documents.len()
    );
    if p.documents.iter().any(|m| !m.location_syntax.is_empty()) {
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
