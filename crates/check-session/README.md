# denotate-check-session

Reusable checker sessions. A `Session` caches preparation and verification work across
snapshots of the same program, so an editor's warm checks are fast, while guaranteeing
that warm results (and work receipts) equal a cold check of the same snapshot.

`profiling::process_memory` provides best-effort process measurements for drivers.
`MemoryProfiler` samples active checker profile spans every 20 ms and streams
boundary events; it retains no event history. OS lifetime peaks and sampled span
peaks are distinct. These observations never enter queries, receipts or cache keys.
See [memory profiling](../../docs/checker-policies.md#memory-profiling).

- `Session::prepare(&request, &corpus, &keys, &operations)` and `Session::verify(...)`
  mirror the fresh checker entry points. `FreshSession` is the uncached control.
- `Session::prepare_fixed` (or `prepare_fixed_with_validation`) retains the
  assumption-independent fold in Salsa. Its input is keyed fixed schemas, domains
  and deterministic limits; its output contains no arena handles or source spans.
  Binding restores current evidence. The current query covers the whole fixed cone:
  input-dependent edits reuse it, fixed edits recompute it.
- Ground keys are projected on demand from the current graph. Owned local queries
  still include full relevant rule content and original dependencies, so changing
  a body invalidates reuse even if the rule and instance keys stay the same.
  Source schemas and declaration bindings are shared across restriction selections;
  admitted views do not retain complete keyed copies of the graph.
- `Session::prepare_with_fixed` shares residual grounding, indexes and admission
  across requests with the same selected restrictions in that run. Obligation
  groups, notices, verification identity and example policy stay separate. This
  path does not use the optional relation-SCC grounding cache. Original assumption
  validation remains shared within a run and fresh across edits.
- The fold has one recycled slot, retained whenever preparation completes under
  checker limits. It has no byte cap and takes no share of the other cache pools.
  `fixed_stats()` reports execution, reuse, disabled-retention bypass and accounted
  bytes (schemas, output and slot overhead, not RSS). Reset and eviction release
  it; failed or interrupted fold preparation clears it. Residual preparation and
  admission are not retained across edits.
- `Retention::max_entries == 0` disables fold retention and prepares fixed facts
  directly from the current corpus, without reconstruction/export. A zero
  `max_bytes` alone limits the other pools; it does not disable the fold. Retained
  and direct preparation agree on semantic outcomes; chosen evidence may differ.
- `Session::verify_with_metrics` and the checker's corresponding methods optionally
  time the actual notice pass. Metrics reset on entry, stay outside semantic results
  and receipts, and are never cached.
- Retained queries use semantic keys, never arena IDs. Unchanged query inputs reuse
  answers; edits invalidate work at each query's granularity. Source binding and
  run-scoped preparation still execute after trivia-only edits.
- **Other cache retention** is bounded (`Retention`, recycled slots, per-pool byte limits);
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
