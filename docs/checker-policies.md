# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Checker backend | BDD only; cached coarse BDD in editors | Predictable, canonical conditions; good warm reuse |
| BDD input order | Semantic-key order; opt-in reverse and structural orders for diagnosis | Structural order helped only synthetic name-separated shapes; under 0.5% on a production-scale program |
| Relation-SCC grounding | Kept opt-in | Warm-run wins; not yet worth the complexity by default |
| Fixed-fact evaluation | Shared across verifications; one retained keyed fold per session, without a byte cap | Checker limits bound the fold; retain completed work for reuse across edits and report its accounted bytes |
| Admission rewrite order | Commit exact-coverage producer removals before cycle bounds | Avoid analysing cycles that independent support already makes redundant; preserve removals if later bounds exhaust |
| Assumption validation | Ground-validate the union selected by executed verifications | Unselected cones need no grounding; selected cones still share whole-residual preparation |
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

## Diagnostic input ordering

`just check-den ROOT --input-order key|reverse-key|structural` selects a BDD
variable order for that invocation. `key` is the unchanged default; the editor
and scorecards keep it. The schema and zoo runners accept the same option. This
is a diagnostic configuration, not a new limit or a new backend.

Ordering happens after fixed/`within` preparation and grounding, before W or any
input-dependent BDD. Structural ordering traverses the dependency graph, with no
symbolic evaluation: settled rule premises contribute input-support hyperedges,
as do selected assumptions. Input-only uniqueness groups receive extra weight.
Groups disjoint from all other groups are contiguous blocks; overlapping groups
are preferences, and every constraint remains enforced. Eight FORCE placement
passes use integer centers and semantic-key ties, retaining the best weighted
span cost seen. No platform-dependent floating-point ordering is used.

The heuristic charges preparation work and stops at one million cumulative
structural entries or four million traversal/placement visits. These optimization
cutoffs return key order, with the reason and spent work retained in the report.
They bound expanded support and metadata, not bytes or BDD nodes. Global work
exhaustion and cancellation still propagate. CLI progress/profile records expose
`inputOrder` (requested/effective order, fallback, inputs, structural entries,
hyperedges and completed passes); non-default runs also print it on stdout.

The backend configuration includes the requested order. Shared contexts partition
by selection and configuration; the assumption-specialized graph receives the
request's exact map before W is built. Local query inputs retain the actual ordered
input keys, including any completion context, so structural edits and switching
orders cannot reuse a result with the wrong map. Structural ordering currently
recomputes with preparation; choosing a default and an edit-stability policy are
separate work. Witness choices and rewrite-warning inventories may differ, since
guarded candidate priorities also use BDD sizes. Conclusive semantic answers must
agree; compare independent tiny-world oracles as well as completed workload runs.

Measured outcome: structural order cut BDD work sharply on shapes whose input names
separate co-read inputs (the zoo's guarded fan-in and ring), and changed little
elsewhere. On a production-scale lowered program (about 30K inputs) it completes
only with raised cutoffs (the support expansion is quadratic there) and moves BDD
node counts by at most 0.5% in every phase; its guarded-bound storage comes from
the number of retained conditions, not the order. Key order stays the default and
structural order remains a diagnostic; there is no plan to change the default.

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

## Guarded settlement

After producer removal and discharge have no batch, the relevant phase can replace
a cyclic premise by a formula over globally settled atoms, under its rule's guard.
The guard stays executable. Bounds relax the reading producer to its guard so the
certificate applies before and after replacement. Earlier marks alone justify later
ones, and an unresolved external component supplies no value. Existing discharges
run first to preserve their warnings and failure-local budget behavior.

One replacement is allowed per component per snapshot. Expressions use shared
Boolean trees, without distributing conjunction/disjunction into rule variants.
A complete expression has at most 1,024 nodes and depth 64; a certificate retains
at most 8,192 expression nodes across its marks. These are optimization cutoffs:
exceeding one leaves the rule intact, reports an expansion cutoff in progress, and
is not checker exhaustion. Temporary construction, dependencies, proof storage and
traversal charge existing budgets. Real work/node/task limits retain their ordinary
stop or recoverable-skip behavior. A graph rebuild and proof installation are atomic.

Candidate-relaxed bounds are computed under G ∧ W in the premise's live backward
cone. A producer dead under its settled condition contributes no dependency edges;
its summary stays as evidence with an explicit domain-relative live/dead flag.
Temporary cones borrow the round's already-accounted summaries. They retain only
their domain and metadata, not a masked condition per producer. Iteration restricts
each contribution transiently before accumulating per-atom upper bounds and lower
guarantees, avoiding large intermediate unions outside the domain. Successful
certificates own the referenced snapshot summaries individually and retain their
conservative proof charges after the round ends. No whole old round is retained.
The reading producer is relaxed before traversal.
Preprocessing is lazy and charged, and has its own recoverable attempt. Candidates
with an informative guard run before unrestricted ones, then by guard node count
and immediate producer count; ties preserve the existing order. That order now
feeds a bounded lookahead of 32 prepared candidates. Prefer cones with fewer live
atoms, then fewer live producers, preserving the preceding order on ties. A cone
with at least 90% of its current unresolved component's atoms live is deferred
behind cones below that threshold. The denominator is all ground atoms in that
component at the current snapshot, not atoms visited during cone traversal; a
621/622 cone is therefore deferred. Live producer count breaks size ties only.

Only size metadata waits in the window (charged conservatively as 16 condition
slots per entry); cones and inferred guards are released and reconstructed for
the chosen attempt. Vacant slots are refilled before choosing again. If every
prepared candidate is deferred, attempt the smallest anyway. Unexamined candidates
may have smaller cones: this is bounded lookahead, not a global sort. Each window
admits at most 32 preparations, including locally failed preparations. Global
work, deadlines and cancellation can still stop that work. On preparation storage
pressure, release optional ranking metadata, return its candidates to their
original queue, and retry without ranking for the remainder of the snapshot.
The 32-entry window and 90% threshold are provisional; neither changes proofs,
cones or the one-replacement-per-component rule.

One-hop implied guards can strengthen G before the cone is prepared. A negative
unresolved premise excludes the union of its exact producers' settled guards;
a positive one requires the union of all its producers' settled guards. Their
conjunction I is retained with the executable replacement. Original summaries
alone supply the inference; a reading producer contributes only G. The cone uses
I ∧ W. If I equals G under W, or excludes every permitted world, this increment
keeps the existing attempt with G.

Cheap producer-summary hints promote otherwise unrestricted readers. Discovery
runs only when reached, with at most one refined candidate waiting for its new
priority; others retain their ordinary priority while it waits. A candidate
selected from the lookahead reconstructs its guard independently; at most that
candidate and one waiting discovery retain inferred guards. It stops after
8,192 visited summary/body/expression units per candidate and uses the existing
1,024-node/depth-64 expression caps. BDD operations retain the existing per-operation
limits and global work charges. A most-recent signed producer union is shared
within the snapshot. Its metadata, temporary expressions, conditions and owned
source snapshots charge condition-node slots conservatively; intermediate charges
are released together after discovery. Cone preparation evicts this optional union
as well as optional bounds before retrying under storage pressure.

An inference cutoff or recoverable BDD/storage failure discards partial inference
and returns to G and its ordinary priority. Progress records `implied-guard`
attempts/skips/cutoffs. A failed inference does not itself make the fallback's
region inconclusive; subsequent proof attempts determine that result. Global
work, cancellation and deadlines propagate. Discovery is one hop, not a fixpoint,
and does not replace the preceding unrestricted bounds/removal/discharge passes.

One snapshot-local cache entry retains the latest complete bounds or failure key.
If preparing the next cone hits storage pressure, discard the optional cache and
retry preparation once under the same cap, retaining all work charges. A repeated
failure is the ordinary local skip. Reuse requires the same domain representation, cone, component, snapshot and
relaxed rule (omitted when its head is outside the cone). Metadata conservatively
uses condition-node storage slots as well as work charges. Different guards never
inherit another guard's failure. Replacing an entry releases it; successful proofs
retain their own certificates. No result cache crosses snapshots. Repeated signed
atoms in one body need only one attempt. Progress distinguishes
`guarded-preprocessing`, `guarded-bounds` and `guarded-settlement`, with per-candidate
cone size, preprocessing/iteration elapsed time, reuse and outcome. Progress also
records whether ranking deferred the candidate, its component atom count, and its
actual bounds-attempt position (absent while it is waiting). Saved reports retain
the deferral flag even if the candidate later runs. Expression
`cutoffs` remain separate. A replacement still invalidates failed/negative attempts.
Preparation also reports domain BDD size and existing versus added condition-node
storage, including partial visited/live counts on failure. Added storage is the
amount successfully retained before cleanup, not the failed requested increment
or a byte measurement. These counters do not alter limits. Deduplicated BDD payload,
process RSS and physical footprint are separate measurements; none is inferred
from the conservative condition-node allowance.

Default warnings use the existing eight-note/sixteen-location caps, with at most
32 expression nodes rendered per formula and explicit omission counts. Full
`--verbose` evidence includes guard, settlement ranks, supporting component
rules and each implied guard's producer conditions. Inferred sources outside
the replaced premise's cone remain owned proof dependencies. Stable/supported-model oracles and fresh/cold/warm tests are correctness
gates; CLI benchmark timings and sampled memory remain measurements only.

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

Admission prioritizes unresolved negative components and their blocked providers
(phase `relevant`). Only after that work reaches a fixed point does phase
`downstream` attempt removals on other still-blocked heads and discharge redundant
input negations on settled rules. The latter also runs without cycles when selected
assumptions can justify warnings. Each phase keeps the existing structural,
exact-coverage, strengthened-bound, discharge, then guarded-settlement ordering. Relevance is recomputed
after commits. Targets and support differ: proofs keep all providers they need,
including settled components, while unrelated structural worklists, evaluation and
summaries wait. Graph maintenance and the full input universe/W remain shared;
proof conditions retain the original variable order and universe for replay.

Phase A exhaustion retains the ordinary admission limit. Global/shared logical
exhaustion in phase B instead sets `downstream_incomplete`, with phase/resource details, and
leaves cycle admission classifications intact. It produces an Information diagnostic
at the verification and an optional summary field; it does not change verdicts or
exit codes. Same-context admission reuse retains this marker and its receipt under
the same logical limits. Deadlines/cancellation still abort and are never cached.
Phase B has no new allowance: both phases share the existing budget. Committed
batches survive exhaustion; pending batches remain transactional.

Ordering can remove warnings: a downstream producer that becomes exact after a
cycle is resolved is no longer a removal target. Preserving those warnings would
require a separate lint policy. Existing finding identities and proof rules stay
unchanged; each migration records the observed warning differences.

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
or bound-removal notes and sixteen related locations, after provenance union, with exact
omission counts. Notes use lexical order; retained locations use immutable source
span/label order. Legacy symbolic coverage/discharge locations remain unbounded and
are protected in mixed warnings. Full detail removes these display caps. These are
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
covers the proof passes. Progress distinguishes `producer-removals`,
`guaranteed-bounds`, `bound-removals` and discharge `candidates`/`upper-bounds`.

After cheap removals have no batch to commit, a recursive component with a
non-exact candidate and exact head coverage can use strengthened bounds. Its lower
guarantees are unions of existing exact producers only. Upper bounds descend from
true, restricting internal negative premises by the complement of those guarantees.
A candidate is redundant when its complete body's upper bound is covered by the
head's exact producers under W. These exact producers remain in the graph; no
recursive lower cover or new settled meaning is inferred. Supported-model upper
bounds, including positive self-support, remain the contract. Bound removals commit
before discharge, so later snapshots can expose further exact producers.

Guaranteed bounds are computed once per eligible component in the snapshot and
released after its last candidate. Their producer summaries, guarantee unions,
old/new bound maps and retained proof conditions charge existing work/storage
limits. A successful proof retains its component certificate through an `Arc`,
conservatively charged per proof as for discharge certificates; covering summaries
are still cloned. Default evidence shows exact head-cover producers, with the same
per-warning display caps as structural evidence; full component support is expanded
on request. This can retain substantial metadata in a large component and is not a
memory optimization. An unsuccessful strengthened pass may be followed by legacy
discharge bounds. Neither computation nor its temporary cache crosses snapshots.

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

Admission recovers from per-operation BDD task/node failures inside individual
proof attempts: exact-producer coverage, a removal check, component bounds,
guaranteed bounds, a bound-removal check, or a discharge check. Failed temporary
conditions and their retained-node accounting are released. Work stays consumed:
a failed condition preflight is charged its task
allowance plus one stopping step, with no construction charge. The bound is still
`min(max_bdd_tasks, remaining_work / 2)`; when remaining work is the tighter bound
or ties it, failure reports `BDD preflight: work` and stops admission. Successful
operation charges are unchanged. Completion-equation preflights are unchanged.

Temporary upper/guaranteed/guarded bounds and guarded-cone preprocessing also
recover from condition-node storage exhaustion, releasing all partial storage.
This exception does not apply to proof installation or shared evaluation; it does
not raise or bypass the storage cap. Earlier global work remains charged, so a
later unrestricted bound can still exhaust work before another guarded attempt.

Failures in shared symbolic evaluation or summaries, total work limits and other
retained-storage limits stop the current phase, with the separate downstream marker described above.
Deadlines and cancellation still abort the whole invocation. No pending batch
is salvaged on these failures. Local skips allow independent proofs to commit.
Retry tracking uses ground identities stable within the preparation, not changing
component handles. Bounds, bound removals and discharge keep conservative
invalidation: any rewritten head in their old dependency cone invalidates them,
through either sign and even
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

Completed negative producer-removal, bound-removal and discharge attempts are
also remembered for this admission invocation. They follow the same invalidation
rules as skips; conservative cone changes can retry bounds/discharge even if the
computed conditions would be equal. Cache lookup costs one work step. Cache
invalidation is charged as above, now including remembered negatives. Entries hold
only an attempt identity and head, with bounded observational history when progress
is enabled: no producer lists, BDD conditions or cross-round successful results.
Obsolete attempts are removed and all metadata is released when admission ends.
Negatives never become skip records, exhaustion counts or inconclusive findings.

The negative lookup precedes per-head coverage and component bounds, so no such
prerequisite is built solely for cached consumers. Shared symbolic evaluation and
summaries still run each round. Profiling/progress aggregate run reasons, outcomes
and elapsed time per attempt kind and round; coverage/bounds time is separate from
proof operations and from symbolic/summary time. These observations do not enter
receipts or retained checking results. Finer skip invalidation and retaining
successful intermediate conditions across rounds remain separate measured work.
Saving work can improve bounded outcomes; cache bookkeeping can also cost work
when little is reused. Compare complete runs for proof/diagnostic equality and
review constrained-limit differences against semantic oracles, rather than
requiring identical exhausted paths or receipts.

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

`peakAccountedConditionNodes` is the maximum accepted condition-storage accounting
observed within a span, excluding rejected demands. It is a peak of the checker's
individual accounting pools, not their sum, physical BDD live storage or heap
bytes. Nested spans observe the same events. The zoo reports this maximum beside
cumulative `bddResultNodes` for each phase; neither is a timing or memory golden.

Stages separate fixed runtime reconstruction, evaluation, export and binding;
residual preparation, including `grounding` and `graph-and-components`;
`input-key-order` and semantic-key construction; each admission round's symbolic,
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

The `.den` CLI additionally writes `type: "progress"` records with its existing
structured phase/admission observations, including sizes before and after admission,
and a terminal `type: "run-end"` record with the checker exit code and optional error.
These are additive record types; the fields of `type: "profile"` are unchanged.
No terminal event means completion was not observed, not success. `--no-progress`
suppresses human stderr output while keeping these profile observations.

`just bench-den-schema` uses the actual CLI and a synthetic Shipping News format
tree, rather than session APIs. It shares the `profiling` build between sampled and
ordinary runs and never raises limits implicitly. Sources, effective configuration,
partial logs and reports are retained even for exhaustion or process termination.
See the [schema benchmark](../crates/ir-text/examples/schema/README.md) for its
explicit semantics, small oracle-checked presets and production-scale target.

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
after the counts to include ground validation and its early fixed/residual preparation,
timed together and shared with all requests; `--two-selections` alternates two restriction sets and
`--no-retention` measures direct fixed preparation. The
scorecard's direct API timer instead includes lazy ground validation when needed.

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
storage. Program-level validation is outside the scorecard's phase timers. When a
cone needs grounding it now includes the fixed fold and residual preparation; later
requests reuse both. The CLI memory profile reports the nested `fixed-evaluation`,
`residual-preparation` and `assumption-specialization` spans. Compare total preparation
and overall peak footprint, not validation time alone or sums of nested spans.

Validation and W share one view specialized by exact fixed truth. The original
residual remains for admission/evidence; the specialized view retains its own residual
rules and dependency graph, sharing fixed evidence. Both are run-scoped. The fold
has its own allowance; residual grounding, specialization and the cycle index share
an independently bounded validation allowance and `AssumptionValidation` receipt
which depends on `FixedFacts`. Request attachment and W remain charged to preparation.
Default ceilings are unchanged. Exhaustion is inconclusive and interruption does not
install partial preparation. Direct and optional relation-cache requests requiring
ground validation use this same fold; other direct requests remain unfolded controls.
There is no cross-edit validation cache, even when a session reuses the fixed fold.

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
