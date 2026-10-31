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
re-scored with the `.den` scorecard. That scorecard is still on the roadmap and is a
prerequisite to this decision. An alternative must demonstrate better conclusive outcomes
under comparable limits, while matching the independent semantic oracles; inconclusive
or unsupported answers are not wins. A second backend is not a standing feature-parity
requirement.

## Re-scoring

```sh
just score-test-dsl path/to/program.testdsl \
    --edit path/to/edited.testdsl --json /tmp/scorecard.json
```

Only the first file is required. Without `--edit`, the command appends an unrelated
mapping as a labeled, reproducible fallback edit; supply a real edited program for
meaningful numbers. `--samples N` (default 5, after one warm-up), `--timeout-ms N`
(default 60,000), and `--unconstrained` (lifts session retention limits only) are
available. Run it alone for useful timings.

It reports cold, trivia-warm and semantic-edit timings for uncached global BDD, fresh
local BDD, cached BDD (with optional relation-SCC grounding),
and controls for planning and grounding reuse. It measures lowering and checker reuse,
**not** parser or LSP scheduling latency. Results are compared against a same-run
global control; conclusive contradictions, warm mismatches and operational errors
fail the command. Unsupported or incomplete checks are never speed wins.

`.den` input support for the scorecard is on the [roadmap](roadmap.md).

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
