# Plain Boolean execution plans

`denotate-plan` is the experimental driver above the checker's stable-query oracle.
It builds a dependency partial order for **explicit output atoms, under one named
verification**, then exports or interprets it. It does not change checking, the
default BDD path, or editor behavior.

```sh
just plan-den ROOT --verification checks --output result
just plan-den fixtures/execution-plan --verification checks --output result
```

Repeat `--output` for more relations. Names follow `.den` name syntax; qualify an
ambiguous name. Output relations expand over the program's resolved domains,
including tuples with no producer. The Rust API also accepts individual atoms and
output priority classes. The command writes JSON, exits 0 only for a complete plan,
and 2 for invalid input, a planning problem, an empty context or exhaustion. It
exports plans; it does not execute a user program.

## Construction and guarantee

`Planner::prepare` owns an immutable program/verification engine. `build` first
requires a permitted input world and **whole-program existence and uniqueness**.
This is deliberately stronger than eventual output-scope meaning: an unrelated
ambiguous or meaningless region can prevent a plan. Successful obligation checks
are not a prerequisite, and building a plan does not prove the obligations.

Only the requested output cone becomes plan work. Input values are available at
entry, but are not assumed true. Fixed values become constants; ordinary rules
become Boolean expressions once their premises are available. Pure positive SCCs
with settled external premises become least-fixpoint kernels. For remaining cycles,
the bounded SAT expression oracle synthesizes an expression over available values.
Expressions can contain runtime conditionals without creating scheduling branches.
There is no global BDD construction or admission rewrite pass.

The correctness argument is induction over availability: input and fixed values
agree with the unique stable model; a rule expression preserves that agreement;
a positive component computes its least model under the already-agreeing external
values; an extracted expression has a checked equivalence over those values.
Thus each newly available value agrees too. Independent ready nodes commute, so
changing their schedule preserves the requested outputs.

The plan has implicit entry (inputs) and exit (outputs). Nodes use semantic atom
keys and declare value dependencies. Direct source rule keys retain provenance;
the `.den` command adds source spans and embedded `loc(...)` descriptors separately.
An extracted expression's sources identify its defining rules, not every rule used
in its SAT proof. A constant with no producer refers to its declaration through its
output key. JSON version 1 is experimental and has no import compatibility promise.

`Plan::execute_permitted` is a bounded reference interpreter. The caller must first
validate its complete input snapshot against domain/cardinality restrictions and
the selected assumptions. **It does not perform input admission.** Every input it
reads must have an explicit Boolean value; missing is an error, not absence. No
runtime permission, strict/run-and-log policy or contract validation is implied by
this low-level API. The CLI does not expose unchecked interpretation.

The interpreter runs computations once and kernels to their least fixpoint.
Semantic-key, reverse-key and output-priority policies choose only among ready
nodes. Priority propagates to output providers and cannot change their meaning.
Tests compare all three schedules with independent stable models on tiny worlds.

## Bounds and remaining work

The existing checker limits bound preparation and each meaning/oracle operation.
Construction separately charges its graph/expression work to `Limits::max_work`
and checks cancellation/deadline between operations; a solver operation has its
own cooperative timeout and can finish after the driver deadline, which is then
reported as inconclusive. `Options` caps plan nodes (100,000) and oracle calls (256),
with the existing per-call `OracleLimits`. The interpreter has an explicit work cap.
The CLI exposes atom/rule/work/time, plan-node/oracle-call and available-value caps;
the Rust API exposes all checker and oracle settings.

Repeated builds reuse only the immutable engine's existing query cache. Edits need
a fresh planner. There is no session integration or reusable plan cache. Semantic
keys identify nodes, not sufficient cache invalidation inputs.

Splits, joins, residual branch states, local BDD strategies, tasks and produced
inputs are subsequent increments. No failed bounded strategy establishes that no
static order exists. `Build::Problem` preserves semantic counterexamples or the
remaining atoms and oracle answer; exhaustion is explicitly inconclusive. Partial
construction never exposes a `Plan`.

This is a ground-level foundation, not yet a corpus-scale performance claim. The
driver indexes the prepared graph, scans worklists for ready values, and can retry
rules after progress. The interpreter and depth exporter also use simple ready
scans. Lifted units, incremental worklists and shared branch partitions need their
own measurements and validation.
