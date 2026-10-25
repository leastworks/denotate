# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Editor default backend | Cached coarse BDD | Predictable, canonical conditions; good warm reuse |
| SAT group backend | Kept selectable (`denotate.backend: "sat"`) | Large wins on programs with many distinct literals |
| Relation-SCC grounding | Kept opt-in | Warm-run wins; not yet worth the complexity by default |
| Plan cache | Small-rule bypass with bounded retention | Avoids caching cost for trivial rules |

Tried and removed: component-level evaluation, which lost everywhere it was measured.

Guarantees that are **not** provisional: cold and warm sessions produce identical
results and receipts; conclusive BDD and SAT answers agree; limits produce explicit
inconclusive outcomes, never silent success.

## Re-scoring

```sh
just score-inputmapping path/to/program.inputmapping \
    --edit path/to/edited.inputmapping --json /tmp/scorecard.json
```

Only the first file is required. Without `--edit`, the command appends an unrelated
mapping as a labeled, reproducible fallback edit; supply a real edited program for
meaningful numbers. `--samples N` (default 5, after one warm-up), `--timeout-ms N`
(default 60,000), and `--unconstrained` (lifts session retention limits only) are
available. Run it alone for useful timings.

It reports cold, trivia-warm and semantic-edit timings for uncached global BDD, fresh
local BDD, fresh SAT, cached BDD and SAT (each with optional relation-SCC grounding),
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
