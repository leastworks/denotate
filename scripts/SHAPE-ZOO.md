# Shape zoo

Run `just bench-den-zoo --sizes 8,16,32 --repeat 3`. Select comma-separated
families with `--family`, change the advisory slope threshold with `--threshold`
(default 1.3), or choose a fresh directory with `--out`. `--samply` and checker
limit overrides after `--` use the existing schema runner. `just test-zoo` runs
fitter tests, tiny semantic/path checks for every preset, and a two-size smoke.
The normal `just verify` gate includes these checks.

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

A profiler end event alone is insufficient: a later phase boundary must confirm
progress, and observed exhaustion or unfinished spans invalidate the affected
phase. Failure progress and status reasons identify the affected phase; without enough
attribution, the latest substantive phase is excluded conservatively. A later
checking exhaustion does not discard completed admission. Earlier completed
phases remain usable. Unsupported regions and an unresolved emptiness target
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
