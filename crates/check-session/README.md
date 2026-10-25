# denotate-check-session

Reusable checker sessions. A `Session` caches preparation and verification work across
snapshots of the same program, so an editor's warm checks are fast, while guaranteeing
that warm results (and work receipts) equal a cold check of the same snapshot.

- `Session::prepare(&request, &corpus, &keys, &operations)` and `Session::verify(...)`
  mirror the fresh checker entry points. `FreshSession` is the uncached control.
- Caches are keyed by semantic keys, never arena IDs: unchanged rules and components
  are reused across edits, trivia-only edits re-execute nothing, and an edit
  invalidates exactly the dependent work.
- **Retention** is bounded (`Retention`, recycled slots, per-pool byte limits);
  oversized entries bypass the cache. `without_retention_limits` exists for
  measurement. `reset` and `evict_values` drop cached state.
- **Optional mechanisms:** owned join-plan caching (on, with a small-rule bypass) and
  relation-SCC grounding (`with_grounding`, opt-in). See
  [checker policies](../../docs/checker-policies.md); both are provisional.
- Interrupted queries never retain partial results; recovery recomputes and matches a
  fresh run.

Editors hold one session per program through the shared scheduler in
`denotate-editor`, keep it warm while a program is temporarily uncheckable, and
release it only when the program disappears.

## Scorecard

`examples/scorecard.rs` (`just score-test-dsl`) re-scores the retained paths on a
program; see [checker policies](../../docs/checker-policies.md). It needs the
`test-support` feature, which the recipe enables. Its own tests:

```sh
cargo +1.93.0 test --release --locked -p denotate-check-session --features test-support --example scorecard
```

## Tests

```sh
cargo +1.93.0 test --locked -p denotate-check-session
```

Regression inputs live in `fixtures/regression/` (semantic outcomes and edit pairs,
with no receipts, budgets or witness choices) and in the test DSL's corpus
([test-dsl/fixtures](../../test-dsl/fixtures/README.md)).
