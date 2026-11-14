# Incremental-schema benchmark

`just bench-den-schema` generates a synthetic format tree in Shipping News
vocabulary and runs the real `.den` CLI. It measures preparation, admission and
checking without needing a private program. This is a profiling workload, not a
new tutorial lesson or a claim to implement another DSL's semantics.

```sh
just bench-den-schema
just bench-den-schema --encoding ambiguous
just bench-den-schema --encoding negated
just bench-den-schema --encoding assumed
just bench-den-schema --encoding assumed --overlaps
just bench-den-schema --help
```

The recipe builds both executables once with Cargo's `profiling` profile, before
measurement. Sampling and ordinary runs use the same CLI binary. Add `--samply`
to save `cpu.json.gz` beside the report; it requires the same `samply` installation
as [the profiling recipes](../../../../DEVELOPMENT.md#profiling).
Sampling adds overhead, and the report records whether it was enabled.

`--input-order key|reverse-key|structural` forwards the diagnostic BDD layout to
the CLI (default `key`). `run.json` records the requested order;
`report.json.inputOrderDetails` records the effective order and any fallback.
Compare separate runs with identical shape and limit flags. The order can affect
costs, witness choice and rewrite-warning inventory, but not conclusive semantics.

Each invocation creates a new persistent directory under `target/bench-den-schema/`.
Use `--out DIR` to choose it; an existing directory is rejected. The files are:

- `program/den.root` and `program/schema.den`: the exact generated input;
- `run.json`: knobs, effective limits, revision, whether tracked edits existed,
  build profile, sampling choice, command, launcher exit/signal and wall time;
- `stdout.txt`, `stderr.txt`: full CLI summaries and progress;
- `memory.jsonl`: flushed memory spans, structured progress and terminal status;
- `report.json`: outcomes, sizes before/after admission, remaining cycles,
  admission-round snapshots, completed phases and unfinished spans.

The runner returns success when it records a run, even if checking finds errors or
exhausts a limit. Read `checkerExitCode`, `checkerError` and `outcomes` for the
checker result. A missing terminal event is explicitly `checkerFinished: false`,
including when a sampler exits successfully. Fields that were never observed stay
absent; they are not invented zeros. Source, configuration and partial logs survive
checker failure or termination. If the runner itself is interrupted, recover with:

```sh
just bench-den-schema --summarize target/bench-den-schema/RUN
```

`activeResidualRuleInstances` counts surviving executable residual rules. The raw
`fold.residual.ruleInstances` inventory also retains removed rule slots for evidence,
so it can stay unchanged after admission. `ground.ruleInstances` combines surviving
residual rules with fixed evidence. These counts are not retained heap bytes.

Reports preserve individual phase records; nested phase times and sampled peaks
must not be summed. A completed span can have exited on exhaustion. BDD result
nodes are cumulative work, not peak live memory. RSS and footprint remain separate.
See [memory profiling](../../../../docs/checker-policies.md#memory-profiling).
The observer adds no checking pass and changes no deterministic limit.

`--sat-probe` forwards the opt-in uniqueness diagnostic to `check-den`, before
admission. Each verification/component's latest record is kept in `satProbes` in
`report.json`, including recovered runs. Optional `--sat-probe-timeout-ms` and
`--sat-probe-refinements` follow `--` with the checker limits. SAT requires a
concretely verified pair; UNSAT establishes at most one meaning and says nothing
about existence. Normal outcomes and exit codes are unchanged. Reports contain
local names, worlds and source locations; see the [probe policy](../../../../docs/checker-policies.md#diagnostic-sat-probe).

`--sat-probe-candidates` enables the admission-time guarded-candidate filter;
`candidateProbes` keeps its cumulative counts and per-candidate supported pairs.
The three `--sat-probe-candidate-{limit,timeout-ms,work}` overrides follow `--`.
These allowances cover a whole admission invocation, independently of normal
checker budgets. `not-ruled-out` is not a certificate. The report and recovery
preserve this distinction and unexamined counts.

## Synthetic semantics

A raw message assigns at most one value to each field. One selector field per tree
level chooses among `width` values; selectors and unused payload fields have
optional root declarations. Other fields are read by leaf terms. Those fields
belong to the first child of each leaf-level parent, distributed in round-robin
order. Every third read field has an `absent` declaration; the others are
`required`. Required fields test presence, absent fields test absence. Optional
fields have no presence constraint. Every declaration allocates the message as
source of truth, even when the raw field is absent.

Terms are lowered as “no constraint unsatisfied.” A child's constraints include
its parent and its selector. For example (fragments of one generated program):

```den
relation term1();
relation unsatisfied1();
term1() :- !unsatisfied1();
unsatisfied1() :- !term0();
unsatisfied1() :- !visible(f0, choice0);
unsatisfied1() :- !visible(f1, present); // required
// An absent constraint instead contributes: unsatisfied1() :- visible(f3, present);
matches(format1) :- term1();
```

Declarations add expectations; they never override another declaration. Root
expectations therefore hold for all descendants. `inherits` is the fixed
leaf-to-ancestor table used to determine which leaves expect a field:

```den
declaration(format0, f0, optional);
declaration(format1, f1, required);
expected(F) :- declaration(T, F, K), matches(T);
leaf_expects(T, F) :- inherits(T, A), declaration(A, F, K);
```

The shadowed-definition knob adds conditional expectations whose unconditional
source already exists. It models `if <condition>` as an additional producer:

```den
relation shadow0();
shadow0() :- visible(f1, present);
expected(f1) :- term1(), shadow0();
```

Visibility requires both a raw value and acceptance:

```den
visible(F, V) :- raw_value(F, V), accepted(F);
```

The four encodings vary how acceptance is established:

1. **ambiguous (v1):** `accepted(F) :- expected(F);`. A term can depend on the
   field whose acceptance it supplies. The small reference preset is unsupported.
2. **coverage (v2):** adds acceptance when no matching leaf lacks the field:

   ```den
   may_lack(F) :- expectable(F), leaf(T), matches(T), !leaf_expects(T, F);
   accepted(F) :- expectable(F), !may_lack(F);
   ```

   The small preset's other sibling is decided independently of the payload. That
   coverage admits the self-dependent branch. With no matching leaves the coverage
   premise is vacuously true; it does not establish recognition.
3. **negated (v3):** coverage plus `unsatisfied2() :- term1();`, an explicit
   “not the sibling” constraint. It is ordinary negation, not a priority rule.
   The small reference preset remains admitted.
4. **assumed:** guesses acceptance for the condition-read payload fields only.
   The selectors and unread fields retain their root expectations. The fixed
   `unguessed` table restricts the ordinary acceptance rule by a positive join,
   keeping the assumption's ground cone stratified before admission:

   ```den
   input assumed_accepted(field: Field) within expectable;
   accepted(F) :- assumed_accepted(F);
   accepted(F) :- unguessed(F), expected(F);
   inconsistent_acceptance() :- assumed_accepted(F), !expected(F);
   inconsistent_acceptance() :- expectable(F), expected(F), !assumed_accepted(F);
   assumption consistent_acceptance: empty(inconsistent_acceptance);
   assumption recognized_message: at_least_one(recognized, group_by: ());
   ```

All encodings select `one_value_per_field`. Only assumed acceptance selects
consistency and recognition. Recognition is `recognized() :- leaf(T), matches(T)`;
it means **some** leaf, not exactly one. Each parent has an `empty(overlap)`
obligation checking pairs of children. Distinct selector values make siblings
exclusive in the valid presets. `--overlaps` makes two siblings use the same
selector; the small assumed preset then reports a counterexample.

Cyclic encodings deliberately do not assume recognition: an assumption cannot
rely on admission of its own dependency cone. Consequently these encodings have
different permitted-world contexts; their full statuses are not parity claims.

The independent test oracle decides recognition from raw selectors and required /
absent checks before introducing guesses. On the tiny valid assumed presets, it
exhaustively checks that recognized messages have exactly one consistent guess,
equal to the reference acceptance, and rejected messages have none. It also checks
replayed expectations. This is a workload test, not a framework determinacy feature.

## Shape controls and scale

`--fields` includes the `depth` selector fields. `--reads` counts additional payload
fields; it must fit within `fields - depth`. `--depth` and `--width` create a full
format tree. The generator rejects trees over 100,000 nodes rather than truncating
one silently. The default shape has 6 fields, 2 payload reads and a depth-1,
width-2 tree. Default limits are unchanged.

`--topology coupled` adds cross-field reads between the otherwise separate leaf
conditions; `mixed` adds them for alternating fields. These controls create
separate versus connected cycles in the ambiguous encoding. Coverage can itself
connect components through `may_lack`, so the actual measured components are the
source of truth. Arbitrary coupling need not have a valid evaluation layout or
unique guesses, and larger presets are not promised admission. A coupled read
can look like this, where `f3` belongs to another branch:

```den
unsatisfied3() :- !visible(f3, present);
```

`--shadowed` controls extra conditional producers. `--wide-heads` and `--producers`
add wide input-dependent heads feeding conditional expectations in the field's
owning leaf; each producer reads a payload and a fixed catalog entry. These are
additional producers for existing declarations, so inherited leaf expectations
stay authoritative. `--catalog` and `--catalog-layers` control additional
fixed facts and propagation. `--computed` adds separate task-result inputs and
computed elements; they never share the message fields' sort or expectations.
They model extra input volume, not task scheduling or function bodies.

A moderate run:

```sh
just bench-den-schema --fields 200 --reads 16 --depth 2 --width 3 \
  --encoding coverage --topology mixed --shadowed 20 \
  --wide-heads 2 --producers 100 --catalog 200 --catalog-layers 4 \
  -- --timeout-ms 30000
```

A production-scale **target**, not a completion guarantee:

```sh
just bench-den-schema --fields 29000 --reads 300 --depth 3 --width 4 \
  --encoding coverage --topology mixed --shadowed 409 \
  --wide-heads 2 --producers 5800 --computed 300 \
  --catalog 30000 --catalog-layers 28 \
  -- --max-atoms 10000000 --max-rules 20000000 \
  --max-dependencies 100000000 --max-work 2000000000 \
  --max-bdd-variables 60000 --max-bdd-nodes 10000000 \
  --max-bdd-tasks 10000000 --max-condition-nodes 100000000 --timeout-ms 120000
```

This combines roughly 29K raw input atoms, hundreds of condition reads, two wide
heads and millions of fixed inherited expectations/catalog facts. It is a shape
for local profiling, not a reproduction of private counts or rules. Start smaller.
Add `--generate-only` to save a target's sources without checking it. Limits after
`--` are validated by the CLI's own parser and recorded before launching; none are
raised automatically. `just verify` runs all four small encodings through the CLI,
the oracle, topology and overlap checks, and partial-report recovery tests.

## Layout-valid layered topology

`--topology layered --coupling-percent 50` moves payload allocation to the parent
of its previous owning leaf. That parent declares the field optional; the leaf
retains its explicit required/absent value tests. First classify internal formats
using root-allocated selectors, then decide every payload's acceptance, then run
leaf tests. A matching owner supplies acceptance directly. A nonmatching owner
rules out **all** its expected producers: the declaration, shadowed definitions
and wide producers all require that same owner. No speculative field visibility
is used for these decisions. The recorded layout and prerequisites are in
`run.json`/`report.json`, alongside layout depth and cross-read count.

For example, classify parent A from the selector; accept its optional field f2
iff A matches; then evaluate leaf B's read of f2. When A does not match, raw f2
is invisible even if present. When A matches, changing raw f2 can change B's
recognition. With depth 2, other parents can fail independently; with depth 1,
root allocation also permits tests of accepted-but-absent fields.

The first requested percentage of payload indices (rounded up) introduces a read
of the next payload cyclically in a sibling of that payload's original owning
leaf. This sibling has no local presence test on the payload, so the new read
can change recognition without duplicating or contradicting a local test. All
these acceptance decisions precede every leaf. Connectivity need not produce
a large SCC. Existing coupled/mixed topologies remain exploratory. Assumed
acceptance is checked exhaustively against an independent selector/visibility
oracle; coverage is measured under its different permitted-world convention and
is not promised the same admission result. Assumption validation uses the existing
fixed-truth specialization; no new checker admission policy is introduced.

```sh
just bench-den-schema --topology layered --coupling-percent 50 --encoding assumed \
  --fields 2000 --reads 64 --depth 3 --width 4 --shadowed 409 \
  --wide-heads 2 --producers 5800 --computed 300 --catalog 4000 --catalog-layers 8 \
  -- --max-atoms 500000 --max-rules 1000000 --max-dependencies 5000000 \
  --max-work 200000000 --timeout-ms 30000
```

For independent shape sweeps, use `just bench-den-zoo`; see the
[shape-zoo contracts and report guide](../../../../scripts/SHAPE-ZOO.md).

The report also preserves per-round attempt summaries and cumulative-counter timing
deltas, independently of later progress updates. `guardedAttempts` preserves each
restricted candidate's cone size, preprocessing/iteration times and last state. See [attempt reporting](../../../../scripts/SHAPE-ZOO.md#guarded-bounds-reproduction).
`binarySha256` identifies the measured CLI artifact; the revision and dirty flag
continue to describe the source checkout.
