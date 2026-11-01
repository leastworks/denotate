# denotate-check-session

Reusable checker sessions. A `Session` caches preparation and verification work across
snapshots of the same program, so an editor's warm checks are fast, while guaranteeing
that warm results (and work receipts) equal a cold check of the same snapshot.

- `Session::prepare(&request, &corpus, &keys, &operations)` and `Session::verify(...)`
  mirror the fresh checker entry points. `FreshSession` is the uncached control.
- `Session::verify_with_metrics` and the checker's corresponding methods optionally
  time the actual notice pass. Metrics reset on entry, stay outside semantic results
  and receipts, and are never cached.
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

Coverage uses the shared checker's bounded enumeration and BDD queries afresh
on each check, while reusing preparation. Its results retain the current verification
and resolved domains; no coverage verdict is reused across context changes.

## Scorecard

`just score-den ROOT` (`examples/score_den.rs`) re-scores explicit `.den`
verifications, with optional edited-root measurements and JSON output.
`just score-test-dsl FILE` (`examples/scorecard.rs`) retains the test DSL scorecard.
See [checker policies](../../docs/checker-policies.md). Both need the `test-support`
feature, which their recipes enable. Their tests:

```sh
just test-score-test-dsl
just test-score-den
```

## Tests

```sh
just test-crate denotate-check-session
```

Regression inputs live in `fixtures/regression/` (semantic outcomes and edit pairs,
with no receipts, budgets or witness choices) and in the test DSL's corpus
([crates/test-dsl/fixtures](../test-dsl/fixtures/README.md)).
