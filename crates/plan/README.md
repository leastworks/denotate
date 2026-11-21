# Plain Boolean execution plans

`denotate-plan` is the experimental driver above the checker's stable-query oracle.
It builds a dependency partial order for **explicit output atoms, under one named
verification**, then exports or interprets it. It does not change checking, the
default BDD path, or editor behavior.

```sh
just plan-den ROOT --verification checks --output result
just plan-den fixtures/execution-plan --verification checks --output result
just plan-den fixtures/execution-plan-branches --verification checks --output result
```

Repeat `--output` for more relations. Names follow `.den` name syntax; qualify an
ambiguous name. Output relations expand over the program's resolved domains,
including tuples with no producer. The Rust API also accepts individual atoms and
output priority classes. The command writes JSON, exits 0 only for a complete plan,
and 2 for invalid input, a planning problem, an empty context or exhaustion. It
exports plans; it does not execute a user program.

## Construction and guarantee

`Planner::prepare` retains immutable program, domain and verification inputs.
Grounding, domain/assumption validation and SAT preparation happen at the first
`build`, when the explicit output atoms are known. `relation_outputs` expands the
supplied finite domains before that build. The engine uses the original grounded
upstream union of those atoms, including dependencies removed by later propagation
or subsumption. Every permitted world must have **existence and uniqueness in this
output cone**. Outside rules are not analysed: an unrelated paradox cannot block
a plan, and downstream filters cannot hide ambiguity inside the cone. All selected
assumptions and the full input contract still define W. Successful obligation checks
are not a prerequisite, and building a plan does not prove the obligations.

The underlying checker prepares a verification-local view using input pins proved
by W, and can establish meaning through a bounded one-level partition on an
exactly-one input group. This can eliminate a syntactic cycle from the upfront
meaning check. These input facts are valid only under the plan's selected contract;
original programs and assumptions are not rewritten. The meaning partition is
separate from availability-aware execution scheduling and does not itself emit
plan branches.

Only the requested output cone becomes plan work. Input values are available at
entry, but are not assumed true. Fixed values become constants; ordinary rules
become Boolean expressions once their premises are available. Pure positive SCCs
with settled external premises become least-fixpoint kernels. For remaining cycles,
the bounded SAT expression oracle synthesizes an expression over available values
in the target's transitive producer cone. It then tries removing support values,
keeping a reduction only after another equivalence proof. This is bounded greedy
reduction, not minimum-expression synthesis. Expressions can contain runtime
conditionals without creating scheduling branches.

If extraction cannot finish, the driver ranks available guards by how many internal
cycle edges their two values remove (balanced removal first, then total removal,
then semantic key). It tries the first candidate, validates both paths under the
verification, specializes rules and recomputes ground SCCs. An unknown feasibility
answer never discards a path. A conclusively infeasible arm is omitted and the
surviving work inlined. Otherwise each arm supplies the same declared result
bindings, followed by one shared continuation. Values at a join may differ; only
availability is shared. The parent continues under its original context, without
inheriting either arm's pins or private temporary values. Splits can nest.
There is no global BDD construction or admission rewrite pass.

The correctness argument is induction over availability: input and fixed values
agree with the unique stable model of the output cone; a rule expression preserves that agreement;
a positive component computes its least model under the already-agreeing external
values; an extracted expression has a checked equivalence over those values.
A split reads an already-agreeing value; its feasible arms partition the parent
context, and specialization preserves the original rules' meaning on each arm.
Induction applies within each arm. Each joined binding therefore agrees with the
unique cone model on whichever arm ran, which justifies the shared continuation without
assuming any joined value true. Thus each newly available value agrees too.
Independent ready nodes commute, so changing their schedule preserves the requested
outputs.

The plan has implicit entry (inputs) and exit (outputs). Nodes use semantic atom
keys and declare value dependencies. Direct source rule keys retain provenance;
the `.den` command adds source spans and embedded `loc(...)` descriptors separately.
An extracted expression's sources identify its defining rules, not every rule used
in its SAT proof. A constant with no producer refers to its declaration through its
output key. JSON version 4 explicitly reports `meaningScope` (original cone sizes,
existence-and-uniqueness requirement, and `outsideAnalysed: false`) and nests `then`/`else` regions under a `split` and declares
its `join.outputs`. Node IDs are local to a region: a complete address includes its
semantic branch path. Size reports count branches and joins separately, including
both arms; depth includes the longest arm. The `.den` command renders constant
names as `{namespace, name}`; the generic API preserves opaque frontend keys.
The export is experimental and has no import compatibility promise.

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
Only the selected arm runs, in its own value scope. The execution result also
records the guards and choices of branches taken.

## Bounds and remaining work

The existing checker limits bound preparation and each meaning/oracle operation.
Preparation keeps its own checker deadlines and is excluded from the driver's
elapsed construction time. Construction separately charges its graph/expression
work to `Limits::max_work`
and checks cancellation/deadline between operations; a solver operation has its
own cooperative timeout and can finish after the driver deadline, which is then
reported as inconclusive. `Options` caps plan nodes (100,000) and oracle calls (256),
with the existing per-call `OracleLimits`. Additional defaults are 16 nested splits
(hard safety ceiling 64), 128 attempted splits, 256 candidate guard/component pairs
per ranking step and 64 support-removal trials per build. Both arms' construction
counts against the shared node/work/call allowances, even if later pruned. The node
cap counts operations; reported size additionally counts their implicit joins.
Optional support trials use the oracle-call allowance too. The interpreter charges
branch-scope copying and requires an explicit work cap.

The CLI exposes atom/rule/work/time, plan-node/oracle-call and available-value caps,
plus `--max-split-depth`, `--max-splits`, `--max-split-candidates` and
`--max-support-trials`; the Rust API exposes all checker and oracle settings.

Repeated builds with the same output atom set reuse the scoped engine's query
cache. Reordering outputs or changing priorities does not change that scope. A new
output set drops the old engine before preparing a replacement; failures cannot
publish its stale scope. `Planner::scope()` is available after successful scope
preparation for the latest build attempt, and complete plans retain `Plan::scope()`.
Edits need a fresh planner. There is no session integration or reusable plan cache. Semantic
keys identify nodes, not sufficient cache invalidation inputs.

Joins currently share only the continuation of sibling arms that supply the same
chosen component's bindings. The driver does not memoize or merge unrelated branch
states, or backtrack to a lower-ranked split after failure. A downstream rule may
eliminate an upstream alternative in whole-program models,
but that is not a proof of unique output-cone meaning. Such a cone is refused with
its ambiguity witness. Full grounding and retained evidence still cover the program;
this scope change makes no preparation-memory claim.

Local BDD strategies, slots/writers and sharing the partition with meaning
checks are subsequent increments. No failed bounded strategy establishes that no
static order exists. `Build::Problem` preserves semantic counterexamples, or the
remaining atoms, signed dependencies, path pins, an example stable world and the
oracle answer. The world illustrates the unresolved context, not an impossibility
proof. Exhaustion reports its phase/resource and is explicitly inconclusive; it
does not yet include that residual report. Partial construction never exposes a
`Plan`.

This is a ground-level foundation, not yet a corpus-scale performance claim. The
driver indexes the prepared graph, scans worklists for ready values, and can retry
rules after progress; each branch specializes the output cone again. The interpreter
and depth exporter also use simple ready scans. Lifted units, incremental worklists and shared branch partitions need their
own measurements and validation.


## Pure tasks and produced inputs (Rust API)

`Planner::build_with_tasks(outputs, tasks, options)` accepts explicit `Task`
descriptors. Each has a lowerer-owned qualified key, optional Boolean applicability
atom, ordered Boolean argument atoms, a nonempty set of result input atoms, and
source rule keys for provenance. Multiple tasks cannot produce the same input atom.
No names are inferred, no relation equations are added, and there is no new `.den`
syntax. The example exports a plan and executes both orders:

```sh
just plan-task-example
```

A result is an input to the relational model, but not an executable entry input.
The driver follows both original rule dependencies and the arguments/applicability
of reachable tasks when preparing its scope. This is a transitive closure: an
argument can itself need another task. An unused task's dependencies do not expand
scope. Full grounding, the full input universe and all selected assumptions remain.
Task descriptor edits invalidate the prepared engine even if output roots match.
Scope includes original arguments even if a task later proves inactive; this is a
conservative prerequisite, not a path-minimal meaning check.

Calls run once their applicability and arguments are available. They publish all
results together. False applicability skips the callback and publishes false for
every result; under a proven false path, arguments need not be available. This is
an explicit inactive-call convention for the Boolean encoding, not a conversion of
unavailable values to absence. Results never become entry bindings, constant
computations, synthesized expressions or positive-kernel outputs. Other relational
values can still be computed without a call when their equivalence proof allows it.
Positive relational recursion remains supported; one-shot tasks cannot be iterated
as a least fixpoint.

For this foundation, a scheduling split with tasks keeps the rest of that region's
requested work in each arm. It does not share a task continuation after the join.
Already executed tasks' bindings are inherited; tasks executed in an arm cannot be
forgotten and run again later for a second result. This is conservative, may duplicate
plan structure, and keeps task-state merging out of this increment. Plain plans
retain their existing sibling joins. Callback purity means all ready-node orders
agree on results; callback order is observable only in the execution trace.

`execute_with_tasks` receives entry inputs and a callback. The callback sees only
its task key, ordered argument values and declared result keys. It returns exactly
one Boolean value per result; missing or extra keys are errors. Task failures abort
this reference interpreter. Supplying a task-produced atom at entry is an error,
and `execute_permitted` refuses task configurations without a callback. The task
events distinguish invocations from skips. JSON v4 includes `call` operations and
separate `inputs` / `producedInputs`; call keys and source rule keys survive export.

**Conditional guarantee:** the completed observation (entry inputs plus actual
callback results, false for skipped calls) must satisfy the input contract and W.
Unlike the plain interpreter, this observation is not available at entry. This API
requires pure deterministic callbacks whose results respect that contract; it does
not validate that promise or claim permission to execute. Callbacks must not be
passed counterfactual precomputed results to bypass scheduling. Since a pure call
is demanded only when a required value needs it, unused task results need only
admit a permitted completion. No production execution, strict/run-and-log policy,
writer-conflict handling, mandatory/optional slot arguments or trace-before-use is
implemented yet. Those remain the next task/slot increment.

Descriptor traversal and extra scope closure use existing work/cancellation limits.
Task nodes, split arms and interpreter bookkeeping use the existing allowances.
An arbitrary host callback cannot be preempted by the interpreter's operation cap;
its resource control belongs to the host. No new performance claim or limits policy
is introduced.
