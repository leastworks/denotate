//! Generate and measure a synthetic Shipping News format tree through the real CLI.
#[path = "schema/attempts.rs"]
mod attempts;
#[path = "schema/conditions.rs"]
mod conditions;
#[path = "schema/generate.rs"]
mod generate;
#[cfg(test)]
#[path = "schema/knowledge_tests.rs"]
mod knowledge_tests;
#[path = "schema/outcomes.rs"]
mod outcomes;
#[path = "schema/runner.rs"]
mod runner;
#[cfg(test)]
#[path = "schema/tests.rs"]
mod tests;
// Reuse CLI limit validation and defaults; no second limit policy.
#[allow(dead_code)]
#[path = "support/sat_policy.rs"]
mod sat_policy;
type Failure = (u8, String);
#[allow(dead_code)]
#[path = "check/options.rs"]
mod check_options;
fn main() -> std::process::ExitCode {
    match runner::run(std::env::args().skip(1).collect()) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("bench-den-schema: {message}");
            std::process::ExitCode::FAILURE
        }
    }
}
