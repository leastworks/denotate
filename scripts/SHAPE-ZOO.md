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

## Preset contracts

Each preset has one verification. `n` is the requested size; all other shape
parameters stay fixed. Counts below describe the possible authored ground graph
before admission (fixed evidence included); the report records actual inventory.

| Preset | Variable shape | Atoms / rules | Expected path |
| --- | --- | --- | --- |
| fan-in-fixed | n fixed sources of one head | n+2 / 2n+1 | fixed folding, present-tuple failure |
| fan-in-input | n independent inputs to one head | n+2 / n+1 | symbolic disjunction, replayed failure |
| negative-guarded | n independent mutually exclusive even cycles | 3n / 2n | discharge admits cycles |
| negative-unresolved | n input-free ambiguous even cycles | 2n / 2n | cycles survive folding and admission |
| certification | n even cycles feeding one emptiness target | 2n+1 / 2n+1 | blocked target, observation certification |
| removal-heavy | n independently covered output heads beside an ambiguous cycle | n+4 / 3n+2 | at least n removals, no discharges; replay visits residual output rules |
| presentation | n supported heads with a transitive support chain and cyclic alternatives | 2n+3 / 3n+3 | structural source findings and bounded direct evidence |
| guarded-ring | n linked guard-relative settlement units; grouped priority/readiness inputs | 8n+1 / 8n | one 6n-atom SCC; guard-live cones settle claims even with tight per-operation bounds |
| guarded-fan-in | one guarded unit with n input-pair booked producers | 2n+8 / n+6 | one large bound hits a node limit before aggregate storage fills |
| guarded-worlds | 2n independent exclusive input groups, n guarded producers | 6n+8 / 2n+6 | large W exercises temporary cone storage and retained proof ownership |
| guarded-hub | n lane producers, one reader whose class guard sits in a sibling rule | 3n+13 / n+10 (split reader) | implied guard cuts the shared cycle at its reader |
| schema-layered | n payload reads, n+2 fields; depth 2, width 2, assumed acceptance | linear at fixed tree shape; inherited tables have four leaves | shared layout-valid schema preset |

Categorical changes are distinct families. Fixed facts and removed rules remain
in evidence inventories; executable post-admission sizes are recorded separately.
No semantic outcome, cost counter, timing, or solver witness is a performance golden.
The tiny path checks assert verdicts, surviving SCCs, removal/discharge counts as
path-presence checks, and produced findings, without historical cost thresholds.

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
