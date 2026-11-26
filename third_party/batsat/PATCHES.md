# Local changes to batsat 0.6.0

This is batsat 0.6.0 as published on crates.io (MIT; see LICENSE and the per-file
headers), used through `[patch.crates-io]` in the workspace manifest.

Two changes:

- `src/lib.rs`: `#![allow(warnings, dangerous_implicit_autorefs)]`. crates.io builds
  dependencies with `--cap-lints allow`; a path dependency does not, and upstream code
  trips a lint that is deny-by-default in current Rust.
- `src/core.rs`: `Solver::set_budgets(conflicts, propagations)`, a public
setter for the solver's existing internal conflict and propagation budgets, which 0.6.0
checks at every search checkpoint but does not expose. Denotate's completion checker uses
it to enforce cumulative SAT allowances inside a solve.
