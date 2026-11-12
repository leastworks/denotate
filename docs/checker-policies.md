# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Checker backend | BDD only; cached coarse BDD in editors | Predictable, canonical conditions; good warm reuse |
| Relation-SCC grounding | Kept opt-in | Warm-run wins; not yet worth the complexity by default |
| Fixed-fact evaluation | Shared across verifications; one retained keyed fold per session, without a byte cap | Checker limits bound the fold; retain completed work for reuse across edits and report its accounted bytes |
| Admission rewrite order | Commit exact-coverage producer removals before cycle bounds | Avoid analysing cycles that independent support already makes redundant; preserve removals if later bounds exhaust |
| Plan cache | Small-rule bypass with bounded retention | Avoids caching cost for trivial rules |
| Coverage results | Recomputed each check; preparation is reused | No measured need for a coverage verdict cache yet |

Tried and removed: component-level evaluation, which lost everywhere it was measured.

Guarantees that are **not** provisional: cold and warm sessions produce identical
results and receipts; conclusive answers agree with independent small-world and
stable-model oracles; limits produce explicit inconclusive outcomes, never silent success.

To diagnose a slow or exhausted run, `just check-den ROOT` prints phases, prepared
sizes and the effective limits on stderr, and `--timeout-ms`/`--max-*` override
`Limits` for one invocation ([den-format](den-format.md#commands),
`just check-den --help`). VS Code exposes the same controls through
`denotate.timeoutMs` and `denotate.limits`, window-wide, with automatic rechecking.
These are explicit controls, not new defaults. Both frontends report the failure's
subphase, effective ceiling and observed demand where available. A stopped BDD
operation may not expose an exact count; no count is fabricated. Counts can include
rejected demand, and an effective ceiling can be tightened by remaining work/storage
or backend capacity. These diagnostics do not change accounting or semantic outcomes.

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

Admission progress in CLI stderr and the `.den` editor reports round/stage,
unresolved ground components, affected atoms, current component and committed
rewrites, with a precise final update on exhaustion. It uses existing graph
metadata, not extra admission or BDD work. Inner observations are separate from
the optional memory-profile span stream; both can be enabled together. See the
[progress protocol](../crates/den-lsp/PROTOCOL.md#checking-progress-and-logs).
They do not alter deterministic allowances, cache keys or results. As with other
logging, delivery costs wall time; deadlines remain cooperative.
After admission, progress lists remaining component sizes and bounded cycle
excerpts. Checking then reports the current target and operation, with exhaustion
as soon as it is detected or restored from cache. Recoverable query failures allow
other checks; deadlines ordinarily stop the verification, except for advisory
notices and optional attribution. This changes observation only, not resource
allowances or the existing recovery policy. Finished CLI verification reports are
flushed before later verification work.

Admission starts with a `structural` pass over blocked regions (negative cycles
and their dependents); an already admitted graph has no structural targets.
It reaches a worklist fixed point before committing deletions and running any BDD
proof. After BDD rewrites have admitted an unrestricted program, the existing early
exit avoids another optional round. Truth/falsehood propagation reads current
rule bodies, head producer counts and already settled fixed boundaries; it never
builds a Boolean context. The existing concrete evaluator supplies input-free,
already settled boundaries, including positive recursion, so folded and unfolded
preparation agree. This private dependency-closed evaluation does not select or
validate an input world. Components with discharged premises are excluded from
that evaluation to avoid BDD replay work; propagation can still use their current
bodies. No new unfounded-set or positive-cycle inference is added to blocked regions.

Subsumption expands only positive, single-producer premises. Comparisons stop at
32 expansion levels or 128 visited literals; a cyclic expansion is skipped.
These are optimization cutoffs: skipping a comparison yields no rewrite, not an
inconclusive verdict. Within one head visit, normalized bodies are ordered by size
and deterministic rule order. Exact duplicates use a map; subset searches index
retained bodies by their first signed premise and inspect at most 64 candidates.
For N producers and bounded expansion size K, a visit costs
O(N K log N + N K² + 64 N K log K), rather than an unbounded N² pair scan.
The index can miss a valid subsumption beyond its candidate cutoff. Changes to
producers or structural facts invalidate their reader closure, so a head can be
visited again; the whole pass is still bounded by the ordinary work/deadline limits.
Indexing, propagation, expansion, comparisons, certificate storage and graph commit
are charged. Global exhaustion publishes no partial structural batch. No BDD
condition allowance is consumed by structural certificates.

Structural evidence is a shared flat DAG per pass, trimmed to facts and rules
needed by actual removals. Fixed-boundary source chains are collected lazily from
the retained fixed graph, with charged traversal. Settled helpers may simplify
privately to justify a blocked removal, but their rules are never committed as
removals or warnings by this pass. Warnings preserve per-source-rule instance coverage and
identify supporting/unfolded rules at current locations. Settling chains are not
copied into every retained proof. Ordinary presentation and internal structural
rewrite evidence keys use only direct settling/unfolding support, including
settled premises needed for subsumption. The transitive certificate is traversed
only on explicit request (`check-den --verbose`); that traversal can revisit shared
support across proofs. Symbolic evidence and keys are unchanged. Local session
inputs still close original dependencies, including transitive support; direct
evidence keys do not replace that invalidation boundary.

Per source warning, default presentation retains at most eight distinct structural
notes and sixteen structural related locations, after provenance union, with exact
omission counts. Notes use lexical order; retained locations use immutable source
span/label order. Symbolic related locations remain unbounded and are protected
in mixed warnings. Full detail removes the structural display caps. These are
presentation policies, not checker budgets: proof coverage, verdicts, limits and
`data.finding` identities are unchanged. Coordinate indexes and source hashes are
reused per immutable snapshot within presentation/export; columns still scan the
containing line, so extremely long lines retain a linear per-column cost.
The `admission-structural` profile span is separate from BDD result-node
traffic and retained-condition snapshots.

Within each admission snapshot, producer removal runs before negation discharge.
A nonempty removal batch rebuilds the graph and starts a fresh snapshot; cycle
bounds run only after removals reach a fixed point. The coverage proof and
transactional commit rules are unchanged. This can reduce BDD work and preserve
useful progress before later exhaustion, but changes work charges and may require
extra snapshots. Symbolic evaluation and summary construction still cover the
residual program. No new allowance is introduced; `admission-candidates` profiling
covers both passes, and progress distinguishes `producer-removals` from `candidates`.

Within one immutable admission snapshot, the removal pass computes a head's union
of exact producers only when its first non-exact candidate needs it. Subsequent
candidates reuse that condition and the same ordered producer list. The temporary
union is charged to `max_condition_nodes` while retained, including its accumulator
during construction, and its cache entry is released after the head's last
candidate. The temporary cache never crosses snapshot or verification boundaries;
candidate order and proof policy stay unchanged. This avoids repeated BDD unions
without changing symbolic evaluation or upper-bound iteration. Each successful
removal still clones covering producer summaries into its proof, so evidence
storage can remain quadratic. BDD result-node traffic and retained-node snapshots
do not measure that metadata storage.

Local query construction builds one borrowed head index for original producers and
rewrite proofs on the first query of each verification invocation. Original closure
then visits reached heads with a worklist, rather than rescanning every rule and
proof until no dependencies change. Discharge-context projection reuses the reached
proof keys. The `LocalInput` value, cache identity and logical receipts are unchanged.
Index storage is physical graph metadata, O(original rules + proofs), released after
the local queries; it is not session retention or BDD condition storage and adds no
new limit. Process memory profiling includes it, and `LocalMetrics.keys` includes
construction on the first query. Constraint/domain filtering and the global input
universe required by discharge completion are unchanged. Emptiness and coverage
do not use this local-input path.
The up-front index can cost more than filtered scans for a single tiny query in a
large program; there is no size-based bypass heuristic. Measure that setup cost
alongside the savings from repeated queries and deeper original closures.

Admission recovers only from per-operation BDD task/node failures inside individual
proof attempts: exact-producer coverage, a removal check, component bounds, or a
discharge check. Failed temporary conditions and their retained-node accounting are
released. Work stays consumed: a failed condition preflight is charged its task
allowance plus one stopping step, with no construction charge. The bound is still
`min(max_bdd_tasks, remaining_work / 2)`; when remaining work is the tighter bound
or ties it, failure reports `BDD preflight: work` and stops admission. Successful
operation charges are unchanged. Completion-equation preflights are unchanged.

Failures in shared symbolic evaluation or summaries, total work/storage limits,
deadlines and cancellation still stop the whole admission pass. No pending batch
is salvaged on these failures. Local skips allow independent proofs to commit.
Retry tracking uses ground identities stable within the preparation, not changing
component handles. Bounds and discharge keep conservative invalidation: any rewritten
head in their old dependency cone invalidates them, through either sign and even
when an SCC splits. Coverage and removal use a narrower comparison after the
prospective graph rebuild. Coverage retries when an exact producer enters or leaves,
its settled body changes, or a previously settled head is rewritten in its premise
cone. Removal also retries when its own settled premises change. Rewriting a blocked
premise that stays blocked does not change the summary condition. Comparing current
bodies catches input-guard discharge even when the producer's rule ID is unchanged.

A single scan shares coverage-change detection across failed attempts for each head;
there is no per-candidate copy of its wide producer set. Reader closures are built
only when needed, from pre-commit edges. Metadata work is O(rules + dependencies +
visited premises + skipped attempts), apart from ordered-map/set lookup costs. It
is charged and can stop admission globally before the commit. Unchanged skips keep
their original reason and consumed work; neither graph nor retry invalidation is
partially published if the rebuild or comparison exhausts. No retry cache crosses
preparations, and no BDD values are retained for retry detection.

Admission preserves input variables and their prepared order, selected W and limits.
Unchanged summary operands repeat the same BDD work, while the available preflight
allowance can only decrease. Input/order changes defensively invalidate all skips.
The invariant and the outside-W guard case are recorded in [decisions](decisions.md).

Outstanding skip records travel with the admitted graph and survive shared
admission reuse. Reporting projects current semantic keys and locations. Only skips
whose target lies in a remaining negative component make that region's admission
inconclusive; downstream skips do not contaminate upstream regions. Global summary
skip records are advisory and do not revoke admission achieved by other proofs.
Progress counts all failed attempts, including those invalidated and retried later.
The current record set can therefore be smaller than the progress count.

Concrete replay looks up discharge proofs in a map keyed by ground rule instance
and literal occurrence, maintained with the rewrite proofs on both admission and
local-runtime installation. The map holds only proof IDs and is empty when all
rewrites are producer removals. Lookup is logarithmic in the number of discharged
premises, replacing an uncharged scan over every rewrite proof for each replayed
literal. It adds O(discharged premises) physical metadata, with no new allowance,
semantic key or cached query input; deterministic charges and receipts are unchanged.
Condition-context construction in discharge validation and charged proof scans
remain unchanged. Reusing those requires a separate accounting decision.

### Memory profiling

Phase progress from `check-den` and the `.den` editor includes best-effort process
memory readings. RSS and physical footprint are separate OS metrics; their peak
fields are process lifetime high waters, not peaks attributable to the last phase.
Unavailable readings are `null` (RSS on macOS/Linux, physical footprint on macOS).
These include all live work in the process and are distinct from cache accounting.

```sh
just check-den path/to/program --profile-memory /tmp/den-memory.jsonl
just bench-den-memory --items 1000 --inputs 1000 --width 4 --warm
just bench-den-memory --items 1000 --inputs 1000 --width 32
```

`--profile-memory` creates a new file and streams JSON lines, including starts of
unfinished stages. It works with `--no-progress` and does not change stdout or exit
policy. The optional profiler samples memory every 20 ms while spans are active;
`sampledPeak.rssBytes` and `sampledPeak.footprintBytes` are maxima of boundary and
periodic samples, lower bounds on true phase peaks. The `peak*` fields remain OS
lifetime high waters. Nested spans overlap: their durations and peak sizes must not
be summed. An `end` event means the scope exited, including on failure; the CLI
outcome determines success. Write failures in the profile stream are best-effort.

Stages separate fixed runtime reconstruction, evaluation, export and binding;
residual preparation; semantic-key construction; each admission round's symbolic,
summary, candidate and commit work. Key projection reads the current ground graph
on demand; there is no longer an `admission-key-refresh` stage. `bddResults`,
`bddResultNodes` and `bddResultNodeBytes` count new wrapped BDD results produced within a span.
They are cumulative result payload, **not** allocator traffic or simultaneous live
storage, and exclude the BDD library's internal temporary allocations. Retained BDD
snapshots at symbolic, summary and candidate boundaries deduplicate `Arc` sharing and report
occupied node payload; vector capacity, maps and allocator overhead are excluded.
`Condition` clones share storage; independently computed BDD arrays do not share
their nodes. Memory samples are needed alongside these counters.

The companion benchmark has positive recursion, fixed false producers, four-way
joins, multiple inputs and residual negative cycles discharged during admission.
`--items`, `--inputs`, `--width` (inputs per item), `--layers` (fixed layers), and
`--verifications` vary its shape. Around 30,000 items, 29,000 inputs, width 1 and
28 layers produce roughly three million atoms, mostly fixed. Start smaller: this
is a configurable reproduction tool, not a promise that the full size fits memory.
Its logical limits are explicitly reported (defaults times 100), with a configurable
operation timeout. `--unfolded` and `--no-retention` are separate fresh-process
controls. `--warm` reloads the same source with the session retained and compares
outcomes. `--findings` adds a violation derived through fixed rules; presentation
runs for every verification. Measure through the complete run, since key projection
also serves cache inputs and findings. Profile one process at a time; allocator
retention and profiling overhead
affect observations. No default checking policy changes, timing or memory goldens.

### Outcome scorecards

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

The `.den` scorecard additionally compares `folded-bdd`, the retained preparation
path used by editors. It includes keyed fold projection/binding, with retained fold
reuse on warm/edit runs when the fixed projection is unchanged and retention is enabled.
Samples are still per verification, so they do not amortize preparation/admission
across other verifications. Existing variants remain unfolded controls; the test
DSL variants are unchanged. `preparation_cache.fixed` reports cumulative executed,
reused queries and retained bytes; bypass counts only direct preparations with
retention disabled. The human report also shows accounted retained fold bytes.

Use `just bench-den-fixed 4000 4` for an abstract mostly-fixed workload comparing
unfolded execution with cold and warm folded runs across four verifications. Within
a folded run, each distinct restriction selection prepares and admits once; groups
and results remain per verification. The benchmark asserts outcome agreement and
reports timings and retained sizes, never timing goldens. It also reloads an edit
to an input-dependent rule to measure fixed-query reuse. Add `--ground-assumption`
after the counts to include original ground validation, timed separately and shared
with all requests; `--two-selections` alternates two restriction sets and
`--no-retention` measures direct fixed preparation. The
scorecard's direct API timer instead includes lazy original validation when needed.

The one-shot CLI uses direct fixed preparation, avoiding portable export and
binding while still sharing preparation/admission within its invocation. Editors
retain the session fold; the scorecard keeps its retained/direct controls.

Fold retention uses one Salsa query for the entire fixed cone, with no byte cap.
The session keeps every completed fold under the checker limits and replaces the
previous value when its inputs change. Other cache budgets are unaffected. The old
quarter-of-session allowance made an already-computed fold pay reconstruction and
export costs repeatedly once it outgrew that pool. Checker limits bound work and
atom/rule counts; the retained bytes are accounted separately, not claimed to be a
heap or RSS ceiling.

`Retention::max_entries == 0` disables fold retention. That path calls direct fixed
preparation on the current corpus, avoiding reconstruction/export altogether.
`max_bytes` alone applies only to the other pools. Outcomes agree between retained
and direct preparation; producer/witness choices and transfer receipts may differ.
Reset, value eviction and failed/interrupted fold preparation release the value.

The query input excludes input-dependent rules, but a fixed edit recomputes the
cone; per-relation SCC reuse is not implemented. The retained value stores original
instance substitutions and true producers, not duplicate grounded rule bodies.
Cold reconstruction/export and warm source binding still have costs; re-score them
on real programs. Original validation, eligibility, residual grounding and admission
remain fresh across snapshots. Checker ceilings and admission semantics are unchanged.

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

- **Preparation:** including selected-assumption evaluation and source-schema/group indexing.
- **Admission:** admission rewrites; keyed content uses the current graph without rebuilding.
- **Checking:** verification, replay, attribution and session bookkeeping, minus the
  notice pass. `verification_call_ns` records that enclosing call: checking plus
  notices, not an additional phase.
- **Notices:** the actual selected-notice pass inside verification, run once.

Loading, rendering, size inspection and fresh-control runs are outside those timings.
Unreached phases and a missing notice pass are `null`, not zero. Sizes are sampled
after preparation, before admission rewrites: input atoms, ground atoms, rule instances,
components and the largest five by atoms then rules. Counts of selected assumptions,
obligations and notices are included separately. No parser or LSP latency is measured.

The additional `size.fold` reports present/absent fixed facts, retained evidence
atoms/rule instances/components/dependencies, and residual atoms/rule instances/
components. The existing size fields include both parts. The fixed evidence is
currently the full original settled graph plus one derivation per true fact,
shared within the run; it is not a compact proof store or a heap measurement.
Residual grounding still seeds fixed possible tuples to preserve rule and finding
identity, including false guards. Graph indexes are shared within a restriction
selection; group indexes remain per request. This step
reduces repeated executable and symbolic work, not all initial grounding or evidence
storage. Program-level validation is outside the phase timers. The CLI/editor share
its original-graph summary with folded preparation. Direct API callers compute that
summary on the first request needing ground validation and reuse it within the run;
the temporary original graph is released. The unfolded control still checks its own
prepared graph. The validation query has a separate bounded allowance and receipt;
default ceilings are unchanged. No cross-edit validation cache is involved.

BDD figures have distinct meanings:

- `max_per_query_bdd_nodes` is the maximum logical BDD-size observation in the
  available receipts, not a simultaneous memory peak.
- `max_per_query_retained_condition_nodes` is the maximum logical retained-condition
  observation for a query. Shared conditions can be counted conservatively.
- `cache.retained_condition_nodes` counts payload retained in the session's local
  cache after verification. Cache byte counts are also conservative payload accounting,
  not measured heap usage or RSS. Planning, grounding and fixed folding have separate retained bytes.

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
