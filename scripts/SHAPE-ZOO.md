# Shape zoo

Run `just bench-den-zoo --sizes 8,16,32 --repeat 3`. Select comma-separated
families with `--family`, change the advisory slope threshold with `--threshold`
(default 1.3), or choose a fresh directory with `--out`. `--samply` and checker
limit overrides after `--` use the existing schema runner. `just test-zoo` runs
fitter tests, tiny semantic/path checks for every preset, and a two-size smoke.
The normal `just verify` gate includes these checks.

Use `--input-order key|reverse-key|structural` to compare diagnostic BDD layouts
(default `key`). It is recorded in the sweep and child manifests; each run keeps
the effective layout and any structural-cutoff fallback. Use separate output
directories for comparisons, with the same sizes and limits. Semantic conclusions
must agree when conclusive; admission paths and rewrite warnings can differ and
need review. This option does not select a new default.

The recipe builds the profiling CLI and shared runner once. Each repetition is a
fresh process, run sequentially. Every child directory has the schema runner's
source, manifest, profile stream, stdout, stderr and recoverable report. Recover a
child with `just bench-den-schema --summarize DIR`, or rebuild the whole sweep
with `just bench-den-zoo --summarize DIR`. The saved `sweep.json` records requested
runs; `zoo.json` is updated after each child. Recovery includes interrupted
children and keeps missing repetitions visible in the requested counts.

Use `--sat-probe` to retain independent SAT meaning results alongside each run's
BDD outcomes. Queries run after cheap admission reductions with exact settled
boundary conditions. `satProbes` contains the latest record per
verification/snapshot/component,
including during `--summarize` recovery. Probe limits can follow `--`, for example
`--sat-probe-timeout-ms 10000`. No ordinary verdict changes; uniqueness UNSAT
triggers a separate existence search. Its nested `existence` record distinguishes
`every-world`, `no-meaning` (with an input world), `inconsistent-assumptions` and
`unknown`. Each question gets its own configured allowance. See the
[probe policy](../docs/checker-policies.md#diagnostic-sat-probe).

`--sat-probe-candidates` independently enables the guarded-candidate diagnostic
within admission. Runs and recovered reports retain `candidateProbes`, including
answer counts and unexamined candidates. Pass aggregate allowance overrides via
`-- --sat-probe-candidate-limit 128` (likewise `timeout-ms` and `work`).
Ordinary candidate ordering, verdicts and exit codes stay unchanged.

## Preset contracts

Each preset has one verification. `n` is the requested size; all other shape
parameters stay fixed. Counts below describe the possible authored ground graph
before admission (fixed evidence included); the report records actual inventory.

`component-chain` connects two six-atom guarded cycles to a wide downstream cycle
with `n` overlapping candidate producers. Its three cycles admit at defaults.
With a tighter `--max-condition-nodes` allowance, pending downstream removal
proofs can exhaust storage while the two small upstream components still reach
guarded settlement. Progress distinguishes local `component-storage` skips from
global preparation failures. This tests recovery and component order, not an
enforced work share; an individual expensive attempt can still consume global work.

| Preset | Variable shape | Atoms / rules | Expected path |
| --- | --- | --- | --- |
| declared-groups | n declared two-value groups, co-read with outside anchors | 4n+4 / 26n+1 | competing hyperedges formerly interleaved groups and inflated U; structural blocks preserve compact U and masks |
| fan-in-fixed | n fixed sources of one head | n+2 / 2n+1 | fixed folding, present-tuple failure |
| fan-in-input | n independent inputs to one head | n+2 / n+1 | symbolic disjunction, replayed failure |
| symbolic-exhaustion | n input producers, a dependent negative cycle and an independent guarded cycle | n+7 / n+5 | atom-local exhaustion; independent admission and checking continue |
| negative-guarded | n independent mutually exclusive even cycles | 3n / 2n | discharge admits cycles |
| negative-unresolved | n input-free ambiguous even cycles | 2n / 2n | cycles survive folding and admission |
| certification | n even cycles feeding one emptiness target | 2n+1 / 2n+1 | blocked target, observation certification |
| removal-heavy | n independently covered output heads beside an ambiguous cycle | n+4 / 3n+2 | at least n removals, no discharges; replay visits residual output rules |
| presentation | n supported heads with a transitive support chain and cyclic alternatives | 2n+3 / 3n+3 | structural source findings and bounded direct evidence |
| component-chain | two small guarded cycles feeding one n-producer cycle | n+22 / 3n+20 | guarded settlement survives downstream proof-storage pressure |
| guarded-ring | n linked guard-relative settlement units; grouped priority/readiness inputs | 8n+1 / 8n | one 6n-atom SCC; guard-live cones settle claims even with tight per-operation bounds |
| guarded-fan-in | one guarded unit with n input-pair booked producers | 2n+8 / n+6 | one large bound hits a node limit before aggregate storage fills |
| guarded-worlds | 2n independent exclusive input groups, n guarded producers | 6n+8 / 2n+6 | large W exercises temporary cone storage and retained proof ownership |
| guarded-hub | n lane producers, one reader whose class guard sits in a sibling rule | 3n+13 / n+10 (split reader) | implied guard cuts the shared cycle at its reader |
| writer-ring | n writers, configurable lanes, relays and readers; exclusive routes and writer results | inventory recorded by the runner | mutually exclusive contexts cut a negative relay ring; co-read lane flags compete with uniqueness-group placement |
| schema-layered | n payload reads, n+2 fields; depth 2, width 2, assumed acceptance | linear at fixed tree shape; inherited tables have four leaves | shared layout-valid schema preset |

Categorical changes are distinct families. Fixed facts and removed rules remain
in evidence inventories; executable post-admission sizes are recorded separately.
No semantic outcome, cost counter, timing, or solver witness is a performance golden.
The tiny path checks assert verdicts, surviving SCCs, removal/discharge counts as
path-presence checks, and produced findings, without historical cost thresholds.

## Declared groups

`declared-groups` repeats rules reading each group's first value with `left()` and
its second with `right()`. Those edges compete with group contiguity. Compare the
pre-block structural heuristic with the current build using identical sources and
limits; `--profile-conditions` records U construction steps. The checker unit
control additionally measures component masks for at-most-one and exactly-one.
A small U does not guarantee small fact conditions or selected W.

```sh
just bench-den-zoo --family declared-groups --sizes 4,8,16,32 --repeat 1 \
  --input-order structural --out target/declared-groups
```

## Writer ring

`writer-ring` makes `--sizes` the number of writers. `--ring-lanes` (default 8)
controls lanes per writer, `--ring-relays` (default 6, minimum 2) the number of
kinds and relay predicates, and `--ring-readers` (default 1) downstream readers.
All dimensions are positive integers and survive saved-report recovery.

A lane applies when `route(l)`, `fa()` and `!fb()` hold. Routes are mutually
exclusive across writers. Each writer has a declared exactly-one kind result; otherwise an optional received kind supplies
the value. Each kind enables one relay in a negative ring. At most one context is
true in any permitted world, so the ring has one meaning, the emptiness obligation
is proved, and the downstream notice varies. Exhaustion is reported explicitly;
large key-order runs need not complete. This tests both admission and checking.

```sh
just bench-den-zoo --family writer-ring --sizes 2,4,8,16 --repeat 1 \
  --ring-lanes 8 --ring-relays 6 --ring-readers 1 --input-order structural \
  --out target/writer-ring-structural -- --timeout-ms 120000
```

Compare with `--input-order key` in a new directory, retaining the same checker
limits. Each run records requested/effective order and any fallback. Declared route and result groups are contiguous blocks under structural order;
selected-assumption groups remain weighted preferences. Packing a route group can
separate its members from their co-read lane flags, so compare later condition
costs as well as U construction. Neither placement nor node counts are golden expectations. Larger
writer counts may still be expensive; their cause needs separate measurement.

## Tagged-value hub

`guarded-hub --hub-variant tagged --hub-writers W --hub-tag-values V` uses a
`Tag` domain of V values. `--sizes` controls the number of lanes n. Each writer
has an exactly-one result input (selected coverage and uniqueness assumptions),
and each value produces a `tagged(T)` writer candidate. The W × V writers can
fill the initial candidate window before the small lane cones. The workload also
has exclusive classes, routes, received values and a singleton check group.
It uses the split reader and no decoys. This is separate from the default `pairs`
variant: `--hub-values` still means independent input-pair alternatives per lane.

```sh
just bench-den-zoo --family guarded-hub --sizes 53 --repeat 1 \
  --hub-variant tagged --hub-writers 4 --hub-tag-values 32 \
  --out target/hub-tagged-32 -- --max-work 20000000000 \
  --max-bdd-nodes 10000000 --max-bdd-tasks 100000000 \
  --max-condition-nodes 100000000 --max-bdd-variables 1000000 --timeout-ms 300000
```

Repeat with `--hub-tag-values 128` and a new output directory. Saved reports retain
both variant and dimensions. `guardedAttempts` includes extra `lookaheadWork` and
`lookaheadLimit`; use actual attempt positions and component dumps to distinguish
reaching lane certificates from full admission. These are separate acceptance
claims, with no timing or chosen-candidate goldens.

## Guarded writer chains

`guarded-hub --hub-writers 4 --hub-readers 4 --hub-values 2` puts each lane's
class condition behind `lane_when -> lane_use -> triggered -> applies -> tagged`.
`--sizes` controls lanes; writers share their lanes round-robin. Values control
independent input-pair alternatives per lane, not a sort's domain. Readers have
exclusive classes and split class/read statements; `--hub-reader` still controls
the first reader's split/merged form. `--hub-no-routes` removes route exclusivity
without removing class exclusivity. Chains and decoys are separate workloads.
Without these options the original presets stay unchanged.

For example:

```sh
just bench-den-zoo --family guarded-hub --sizes 4,8,16 --repeat 1 \
  --hub-writers 4 --hub-readers 4 --hub-values 1 --hub-no-routes
```

Compare `beforePruningAtoms`/`beforePruningRules` with `coneAtoms`/`coneRules` and
`liveAtoms`/`liveRules` in guarded attempts. `pruning` records completion or a
fallback reason. Optional fallback keeps the original cone. One successful
replacement still starts another round; large chains may spend their budget on
repeated unrestricted bounds or have expensive final meanings even after cones
shrink. This workload measures that limitation as well as the pruning gain.

## Reading the report

`zoo.json` keeps individual runs and per-phase summaries. Durations sum only
non-overlapping top-level phase spans across repetitions of a phase within one
run (including multiple verifications); nested admission rounds are not added to
those parent durations. Memory takes the maximum sampled phase RSS and footprint,
separately. These include retained earlier work, not allocations caused by the phase.
Unavailable memory stays null.

Each completed phase also reports cumulative `bddResultNodes` and
`peakAccountedConditionNodes`, the maximum accepted condition-storage accounting
observed in that phase. The latter excludes rejected demands and is a peak over
individual accounting pools, not their sum or physical live BDD memory. These
measurements retain the same completion counts; old logs without the storage
measure report null. Interrupted phase records remain in the child's profile.

A profiler end event alone is insufficient: a later phase boundary must confirm
progress, and observed exhaustion or unfinished spans invalidate the affected
phase. Failure progress and status reasons identify the affected phase; without enough
attribution, the latest substantive phase is excluded conservatively. A later
checking exhaustion does not discard completed admission. Earlier completed
phases remain usable. A recoverable admission attempt skip alone does not discard
the phase if a later proof completes it; final unfinished/status reasons still do.
Unsupported regions and an unresolved emptiness target
without a resource failure are valid workloads; the word “inconclusive” alone
does not establish exhaustion. Medians/min/max retain completed/requested
counts so a surviving sample is visible. Fits use medians, at least three distinct
positive sizes and positive available values; constant measured sizes do not fit.

Each phase fits time and both memory measures against the knob and a measured
axis: source bytes for loading, findings for presentation, prepared rule instances
otherwise. Other sizes (atoms, inputs, components, largest SCC, removal/discharge
proofs) remain in each run for inspection. A knob slope above threshold with a
measured-size slope below it is labeled “superlinear in knob only.” Flags are
triage signals, never test failures. Small samples and allocator noise can produce
flags; investigate with larger sizes and repetitions before changing the checker.

Fan-out, positive recursion, join-width and source-only sweeps remain later work.

## Guarded-bounds reproduction

`guarded-ring` links copies of the guarded-settlement example with:

```den
booked0() :- kind(), ready0(), priority0(), cleared0();
booked0() :- kind(), !ready0(), booked1();
fails0() :- ready0(), !booked0();
claim0() :- !kind(), !fails0();
```

The last booked relation links back to the first. The remaining inspected/held/
cleared rules close each local negative cycle. The ring makes one strongly
connected component. Descending bounds propagate priority/readiness combinations
around it; the grouped semantic input order makes this representation grow.
Under `!kind`, all booked producers are dead, `fails_i = ready_i`, and the claim
is just `!ready_i`. Thus the wanted guard-relative certificate remains small.
A tiny independent-world check verifies that equation and both stable and supported
model preservation. Larger skipped cases are measurements, not verdict goldens.

```sh
just bench-den-zoo --family guarded-ring --sizes 4,8,12 --repeat 2 \
  --out target/guarded-ring-measurement -- --max-bdd-nodes 128
```

`guarded-fan-in` uses one six-atom cycle with n booked producers, each guarded by
`kind`, one priority bit and one readiness bit. Their union has a large BDD under
the grouped input order, but under `!kind` the same two-atom cone suffices for the
claim. Here `held = inspected`, so after settling the claim, every booked tuple
is false: the large upper approximation does not also force a large final meaning.
Unlike the ring, it concentrates node pressure in one condition instead of
retaining that condition at many heads. Both families remain useful: the ring
exercises total retained storage; fan-in exercises a single BDD operation's cap.

Guarded bounds now prune dead-under-guard producer edges before iteration. At the
128-node setting the ring's previously failing claims can settle; the earlier
unrestricted passes still run and may skip. Global work/deadlines remain limits,
so these examples do not promise admission at every size or allowance.

`guarded-worlds` gives W a linear BDD (2n independent two-choice input groups),
then reaches n producers of `fails` under the reading guard `!kind`. Each reads a
settled `ready_i = gate AND flag_i` and `!booked`; every booked producer is dead
under that guard. Thus only two atoms need restricted bounds. Retaining W masked
into every producer used quadratic storage before iteration even though the final
claim is simply `!kind AND !(OR_i ready_i)`. Temporary cones now borrow summaries
and retain one domain plus metadata; successful proofs own their original,
unmasked summaries. Both per-operation and global limits still apply.

```sh
just bench-den-zoo --family guarded-worlds --sizes 200,300,520 --repeat 2 \
  --out target/guarded-worlds-measurement
```

Each shared report retains `admissionAttemptSummaries` separately from the latest
progress snapshot. They are keyed by verification, phase and round; `complete`
means an `attempt-summary` was seen, not that admission avoided limits. An interrupted round keeps its last observed
counters with `complete: false`. The zoo copies these into each run and its family's
`attempts` table, including outcomes and aggregate elapsed time by kind.

`admissionAttemptSamples` (zoo: `attemptSamples`) takes differences of cumulative
finished-attempt counts and elapsed time. A delta of one is an individual timing;
a larger delta is explicitly a **batch total**, with its count and outcome counts.
No average is labeled as an individual measurement. Single skip events identify
their target head; the stream does not identify the exact rule in general, so the
component's representative rule is never substituted. Reused attempts have no
new execution timing. Truncated streams can leave samples missing; the aggregate
counters remain the authority. Timings are observational, never test goldens.
The manifest records `binarySha256` for the actual CLI artifact used.

Guarded work additionally reports `guardedAttempts`, one latest per-candidate record
per verification/phase/round/index. It contains the reading head/premise and source
location, visited/live cone atoms and rules, domain BDD size, existing/added
condition-node storage, preprocessing and iteration milliseconds, reuse and state.
Failed preprocessing reports partial counts before releasing its storage; an
interrupted running operation can still have null counts. Retained accounting is
distinct from the profiler's deduplicated BDD payload, RSS and physical footprint.
These are actual candidate observations, independent of the older
counter-delta samples. `completed` here means bounds completed, not that settlement
subsequently produced a rewrite.

## Implied-guard reproduction

`guarded-hub` has n producers of `tagged`, each requiring a distinct route, two
input bits, `declared(perishable)` and the cyclic `cleared` relation. A shared
reader combines `declared(hazardous)` with a negated check of `tagged`. The two
declared classes are exclusive. By default, the reader's conjunction is lowered
into separate statement rules, so its class guard is implicit in an exact
producer of `hc_unsat`. One-hop inference retains that class guard and settles
the shared reader, instead of settling one lane in each round.

Use `--hub-reader split|merged` (default `split`) to compare that lowering with a
single conjunctive rule. `--hub-no-routes` removes the at-most-one route assumption;
the class assumption remains. Both settings are recorded in the sweep and report.
The notice on `hazard_claim` varies in every variant; the tiny split case checks
stable and supported models under independently enumerated permitted worlds.

```sh
just bench-den-zoo --family guarded-hub --sizes 53,106 --repeat 1 \
  --out target/hub-split
just bench-den-zoo --family guarded-hub --sizes 53,106 --repeat 1 \
  --hub-reader merged --hub-no-routes --out target/hub-merged
```

Inspect both the reader replacement and the attempt table. Earlier unrestricted
bound passes still run and can dominate at raised BDD limits. A small inferred
guard does not promise cheap admission at every limit or size.

## Cone-order reproduction

`guarded-hub --hub-decoys 12 --hub-decoy-shape full|near-full` adds split readers
before the useful class reader in source order. Their inferred `docked` guard
leaves the wide producer fan-in live. `full` visits the whole component;
`near-full` adds one side atom excluded by that guard. Both exercise scheduling
without changing what a valid certificate must prove.

In this variant the classes are complementary tests of one input bit, and the
held test does not require priority. This keeps the final meaning small even with
`--hub-no-routes`, while full-cone bounds encounter a large intermediate Boolean
function. These deliberate workload choices apply only when decoys are requested.
Options are saved in the sweep and recovered report.

```sh
just bench-den-zoo --family guarded-hub --sizes 53 --repeat 1 \
  --hub-no-routes --hub-decoys 12 --hub-decoy-shape near-full \
  --out target/hub-decoys
```

Inspect `guardedAttempts`: `deferred` and `componentAtoms` explain the ranking;
`position` distinguishes actual bounds attempts from waiting candidates. Compare
admission and downstream work separately. A scheduling improvement can leave
ordinary downstream warning work incomplete at the same limits.

The `repeated-field` family models constant appenders and conditional tasks whose
output-presence bits are inputs, with an `is absent` reader. Each size unit adds
one of each producer. Compare `key` and `structural` orders with condition profiling
to measure the wide presence OR and confirm the effective order in the report.


`knowledge-scc` generates dual positive knowledge-propagation rings, with `size`
decisions in each SCC and one input deciding known true versus known false. The
initial rule order runs against propagation. It checks consistency and queries a
varying decision, exposing repeated scans independently of large BDD conditions.
Use `just bench-den-zoo --family knowledge-scc --sizes 128,1024 -- --profile-conditions`
for in-component records (or generate its source and use the schema runner).
This sparse workload is not a promise of one-pass evaluation for arbitrary SCCs.

## Guarded-schema completion

`guarded-schema` uses the SAT engine with completion semantics and a recognition
hypothesis. It models a forest of format roots and guarded blocks, a field-value
admission loop, task-produced values, and classification feeding back into guards.
Each condition site has its own zero-arity relation. Generic rules join derived
blocks and values against authored statement, field and task tables. This is a
synthetic structural regression, not an implementation of a particular DSL; its
ordinary checks may find ambiguity or violations.

`--sizes` varies `sets` by default. `--schema-axis stmts` varies statement rows per
nested block; `--schema-axis depth` requires `--schema-blocks N` to hold the number
of nested blocks **per format** constant. The latter distributes those blocks
across levels rather than preserving fixed fanout. Depth is a source shape, not a
promise of that many grounding rounds. `--schema-impossible 1` is a separate
control: an empty positive guard disables roots, so deletions must propagate down
the block levels. It should have no accepted observations.

```sh
just bench-den-zoo --family guarded-schema --sizes 275 --repeat 1 \
  --schema-depth 2 --schema-fanout 5 --schema-stmts 3 --schema-triggers 1
just bench-den-zoo --family guarded-schema --schema-axis stmts --sizes 1,3,9 \
  --schema-sets 32 --schema-depth 2 --schema-fanout 5 --repeat 2 \
  -- --sat-max-worlds 0
just bench-den-zoo --family guarded-schema --schema-axis depth --sizes 1,2,4,8 \
  --schema-sets 32 --schema-blocks 32 --schema-impossible 1 --repeat 2 \
  -- --sat-max-worlds 0
```

`--schema-wide 1` widens decisions to recognition, accepted fields, written values,
violations and task activation. It exercises component determinacy with observable
processing results; the default (`0`) keeps recognition and accepted fields.

The first command uses unmodified SAT defaults. The two preparation sweeps use
zero search worlds to avoid spending time on semantic searches after preparation;
their inconclusive checking outcomes are intentional and are not default-limit
verification results. Provider validation still runs. Use the same flags on both
builds. `--check-binary PATH` selects a preserved checker binary; its path and hash
are recorded by the runner. It must support the same CLI options.

Other integer knobs are `--schema-elements`, `--schema-values`, `--schema-reads`,
`--schema-tasks`, `--schema-outs`, `--schema-splice` and `--schema-self`. Splice and
self are percentages (defaults 25 and 50); assignment is deterministic. Defaults
are 2 values per element, 1 read per guard, 5 outputs per task and 1 trigger per
block. Element/task counts scale with blocks unless supplied. `self` changes where
a term's classifying field is first declared; other generated block/task bindings
can still admit or produce that field. It is not a semantic exclusivity promise.
For the 275-format shape there are 8,250 nested blocks and 24,750 statement rows.

Reports include `shape`, completion preparation attempts, stage work and time,
peak temporary possibility counts, top join rules, and `completion` stage fits.
Incomplete preparations keep their records but do not enter completed-stage fits.
The diagnostic least-model comparison is off unless `--completion-size-lfp` follows
`--`. BDD input-order and admission-probe options do not apply to this family.

Completion runs use the runner's `--compact-outcomes`: report summaries omit
`evidence` objects while retaining states, counts, identities and exhaustion
reasons. The original evidence remains in `stdout.txt`. Recovery parses outcomes
as a stream and skips evidence before allocation, so large interpretations do not
have to fit in a JavaScript string. The CLI still constructs and writes that
evidence; its time and disk cost remain part of the whole-process measurement.

`guarded-schema --schema-double 1` adds a direct type-guarded source for each
format's statement field while retaining the existing profile source. With
`--schema-self 100`, every format has the profile/splice double-giving pattern;
`--schema-self 50` keeps the mixed corpus-scale shape. The profile's implication
of the type guard must come from its unchanged equations, not from the head being
pruned. Compare against `--schema-double 0` as the control with no added splice.
Completion reports record scoped producer removals and their W/W+H context.

Pruning is off by default. Keep the generated shape identical and compare the
normal run with one adding `-- --completion-prune` to the zoo command. Only the
opt-in run emits pruning records and uses H-first classification existence.


`guarded-schema --schema-odd 1` is a diagnostic control. It adds
`accepted_field(element_0) :- type_matches(format_0), !accepted_field(element_0);`,
a known guarded negative self-edge beside the family's existing loops. It is
deliberately not a valid lowerer pattern. The zoo regression checks the closed
odd witness, its guard and its exact source line in size JSON, live CLI progress
and verbose human output. The default remains `--schema-odd 0`.
