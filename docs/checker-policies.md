# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Checker backend | BDD only; cached coarse BDD in editors | Predictable, canonical conditions; good warm reuse |
| Relation-SCC grounding | Kept opt-in | Warm-run wins; not yet worth the complexity by default |
| Plan cache | Small-rule bypass with bounded retention | Avoids caching cost for trivial rules |
| Coverage results | Recomputed each check; preparation is reused | No measured need for a coverage verdict cache yet |

Tried and removed: component-level evaluation, which lost everywhere it was measured.

Guarantees that are **not** provisional: cold and warm sessions produce identical
results and receipts; conclusive answers agree with independent small-world and
stable-model oracles; limits produce explicit inconclusive outcomes, never silent success.

## Backend retirement

BDD is the only supported backend. The SAT experiment showed wins on synthetic and
test-DSL workloads, but no demonstrated need on real programs. Maintaining it multiplied
implementation and validation work for each obligation kind and made diagnostics depend
on a setting. Its coverage path still depended on BDD evaluation, so it could not help
when that evaluation exhausted. The implementation, dependency and selectors are retired;
Git history retains the experiment.

Revisit only for a real program that exhausts BDD evaluation within reasonable limits,
re-scored with the `.den` scorecard below. An alternative must demonstrate better
conclusive outcomes under comparable limits, while matching the independent semantic
oracles; inconclusive or unsupported answers are not wins. A second backend is not a
standing feature-parity requirement.

## Re-scoring

```sh
just score-den path/to/program/den.root \
    --edit path/to/edited-program --json /tmp/den-scorecard.json
just score-test-dsl path/to/program.testdsl \
    --edit path/to/edited.testdsl --json /tmp/test-dsl-scorecard.json
```

Only the first root/file is required. `.den` accepts a folder or `den.root`, runs
all explicit verifications through the same request API as `check-den`, and omits
edit measurements unless `--edit` supplies another root. The test DSL command
retains its labeled fallback edit: it appends an unrelated mapping. Supply a real
edit for meaningful edit numbers.

Both commands support `--samples N` (default 5, after one discarded warm-up),
`--timeout-ms N` (default 60,000 per operation), and `--unconstrained` (lifts session
retention limits only; fresh-local remains uncached). Run them alone for useful
timings. The logical limits remain the checker defaults, and `.den` reports the
effective limits and retention configuration in JSON. The scorecards compare global
BDD, fresh local BDD, cached BDD, optional relation-SCC grounding, and controls for
planning and grounding reuse. General assumptions force global verification even
in a session; the `.den` report labels that fallback. Preparation reuse may still
apply, but the variant's name does not imply verdict-cache reuse.

### `.den` measurements

Each sample and variant starts fresh for each verification, then reuses that session
through cold → warm → edit. Warm reloads the same sources with an added comment into
a fresh corpus. Declaration matching uses semantic keys, so file moves do not change
identity. Added verifications have only edit measurements; removed ones have no edit.
Roots without verifications are **unconfigured**, and unselected obligations are
listed. A consistent verification with neither obligations nor notices is a
consistency-only result; a selection containing only notices is labeled separately.

The human table gives median milliseconds and maximum BDD observations across samples.
`--json FILE` also retains every sample, size, outcome, comparison and cache counter.
Checker timing has four non-overlapping phases:

- **Preparation:** including selected-assumption evaluation and key construction.
- **Admission:** admission and refreshed ground keys after rewrites.
- **Checking:** verification, replay, attribution and session bookkeeping, minus the
  notice pass. `verification_call_ns` records that enclosing call: checking plus
  notices, not an additional phase.
- **Notices:** the actual selected-notice pass inside verification, run once.

Loading, rendering, size inspection and fresh-control runs are outside those timings.
Unreached phases and a missing notice pass are `null`, not zero. Sizes are sampled
after preparation, before admission rewrites: input atoms, ground atoms, rule instances,
components and the largest five by atoms then rules. Counts of selected assumptions,
obligations and notices are included separately. No parser or LSP latency is measured.

BDD figures have distinct meanings:

- `max_per_query_bdd_nodes` is the maximum logical BDD-size observation in the
  available receipts, not a simultaneous memory peak.
- `max_per_query_retained_condition_nodes` is the maximum logical retained-condition
  observation for a query. Shared conditions can be counted conservatively.
- `cache.retained_condition_nodes` counts payload retained in the session's local
  cache after verification. Cache byte counts are also conservative payload accounting,
  not measured heap usage or RSS. Planning and grounding have separate retained bytes.

Receipts may describe reused work and include rejected attempts. These figures are
neither fresh allocation counts nor sums presented as memory peaks. Missing observations
remain `null`. Plan, grounding and local-cache statistics expose execution, reuse,
eviction, bypass and retention, with their internal timing counters. Those counters are
subsets of the checker phases, not extra time to add to the total.

Each authored obligation is counted once by kind and verdict, including implicit
trivial uniqueness proofs. Its components and findings are separate: `exactly_one`
can have both a coverage and a uniqueness failure. A known failure remains visible
when checking is incomplete; coverage and emptiness counts are then lower bounds.
Unsupported and no-meaning region counts can overlap. Notices are counted by state
and never become obligation failures. Inconclusive outcomes include phase and resource.
Statistics do not enumerate uniqueness's Cartesian grouping domain; an overflowing
group-total count is `null`, with the verdict still derived from the queried groups.

Comparisons use keyed obligation/component, uniqueness-group, region and notice
outcomes, excluding witnesses. Cold controls warm; an edit also gets a fresh control
of the same variant. Global BDD is an additional fresh control for each snapshot.
Same-path mismatches, conclusive contradictions across paths and operational errors
fail the command. Cross-path differences without a contradiction remain visible in
JSON; unsupported/incomplete runs are never speed wins. Ordinary findings do not fail
the scorecard command: it measures them. Use `check-den` for diagnostics and checking
exit codes.

Run private programs and inspect results in their own work environment. Output uses
ordinary names and paths and is **not an anonymised export**. Bring feature requests
and deliberately abstracted reproductions elsewhere, rather than raw results. The
scorecard does not embed full sources, diagnostic messages or witnesses; diagnostic
quality remains the job of `check-den`.

The existing test DSL scorecard additionally measures lowering reuse and retains its
historical detailed result output and comparison rules.

## Editor latency smoke

```sh
just bench-lsp
```

Real LSP round trips at three program sizes, with no timing thresholds.

## General assumption evaluation

General selected cardinality restrictions are evaluated independently during
preparation, under the existing work, grouping, BDD and retained-condition limits.
An incomplete W is never installed. Its consistency is checked before admission.
The first implementation evaluates fresh whole-program symbolic meaning to obtain
constraint conditions, ignoring unrelated blocked components, then checks through
the whole-program path. This can exhaust on unrelated work; the result is explicit
inconclusive. Restrict evaluation to the constraint cones only when measurements
justify it and the same independent semantics is preserved.

Local verdict caching remains enabled for input-only at-most-one contexts. General
constraints invalidate the absent-extension argument for projecting W into a local
query. Their verdicts are recomputed; grounding and plan reuse remain available.
A future optimization must retain or correctly quantify every external constraint
input and preserve cold/warm results, replay, consistency and cancellation behavior.

## Certification search

Emptiness and coverage can encounter atoms blocked by an unsupported component.
Their search replays a permitted world and may attempt whole-program observation
certification. After processing a world, it excludes all worlds agreeing on the
inputs of the target's structural dependency cone **and every initially blocked
component's cone**. Coverage uses all candidate tuples of the group. Certification
only prunes rules, so later rounds cannot introduce dependencies outside these cones.
An unrelated blocked component can prevent certification; its inputs cannot be
omitted simply because they do not affect the target tuple directly.

This avoids enumerating unrelated inputs for an input-independent blocked cycle.
It does not prove that cycle or change certification's whole-program requirement.
Uncertified worlds remain unresolved. The remaining search condition stays inside
the selected W, including correlations with inputs outside the dependency set.

Dependencies reuse the existing cone analysis, are computed lazily under the
obligation's allowance, and are local to this check. Failure to finish computing
them is explicit inconclusive; a partial set is never used. Diagnostic cone
annotations retain their separate optional allowance. No limits are raised and the
uniqueness path's two-candidate certification policy is unchanged. Search can still
be exponential in the retained dependencies; failure-specific narrowing is deferred.
