//! `.den` checker scorecard. Loading and reporting are outside all checker timings.
#[path = "score_den/driver.rs"]
mod driver;
#[path = "score_den/outcomes.rs"]
mod outcomes;
#[path = "score_den/report.rs"]
mod report;
mod scorecard_support;
#[cfg(test)]
#[path = "score_den/tests.rs"]
mod tests;

use driver::{Config, Snapshot};

fn run() -> Result<bool, String> {
    if cfg!(debug_assertions) {
        return Err("Use --release for scorecard measurements".into());
    }
    let config = Config::parse(std::env::args().skip(1))?;
    let base = Snapshot::discover(&config.root)?;
    let edit = config
        .edit
        .as_ref()
        .map(|p| Snapshot::discover(p))
        .transpose()?;
    config.validate_output(&base, edit.as_ref())?;
    let report = driver::collect(&config, &base, edit.as_ref())?;
    print!("{}", report::human(&report));
    if let Some(path) = &config.json {
        std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap())
            .map_err(|e| format!("{}: {e}", path.display()))?;
    }
    Ok(report["failures"].as_array().unwrap().is_empty())
}
fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
