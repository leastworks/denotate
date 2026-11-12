# denotate-check

The finite relational checker. It grounds a `Corpus` over explicit finite domains,
checks admissibility, replays concrete input worlds, and proves or refutes
`at_most_one`, `at_least_one`, `exactly_one` and `empty` obligations symbolically (BDD), returning
only replayed counterexamples. Runtime dependencies: `denotate-ir`, pinned
`biodivine-lib-bdd`.

## Pipeline

1. **Domains.** `Domains` maps every sort to its typed constants. The checker never
   infers domains from rules; constants used by rules must be in their domain. Empty
   domains are allowed. An input's optional `within` provider is evaluated exactly
   over its input-free, stratified cone before input atoms are seeded. This shares
   preparation limits and fails all-or-nothing with phase `input domains`. Grounding
   uses the complete eligible tuple set; coverage still uses the sort domains.
2. **Preparation.** `GroundProgram::prepare` computes possible atoms and rule
   instances and builds provider-first ground components, keeping original rule, atom
   and argument occurrence IDs. `prepare_with_input_groups` adds input assumptions W
   (`InputAtMostOne` on input relations): permitted worlds have at most one tuple per
   group. `admit` applies justified rewrites.
3. **Admissibility.** Positive cycles are admitted. A negative edge inside an SCC blocks
   that component and its dependents unless a rewrite proves the negation redundant
   under W. Blocked regions are reported (`Unsupported`), never treated as false.
   Each round first performs structural truth/false propagation, dead-rule removal
   and bounded signed-body subsumption through single-producer positive chains.
   Removals target blocked regions; already settled rules supply truth/evidence.
   Structural changes commit before symbolic evaluation, using the same atomic
   graph rebuild. They require no BDD operations. Each settled snapshot then proves
   redundant producer removals from independent
   exact coverage. A nonempty removal batch is committed and the components rebuilt
   before another snapshot; only a snapshot with no removals proceeds to negation
   discharge and cycle bounds. Later exhaustion preserves earlier committed batches.
   Within a snapshot, exact-producer coverage is computed lazily per head, reused
   by its non-exact candidates, and removed from the cache after the last candidate.
   Retained unions count against the existing condition-node limit. Proofs still
   keep their covering producer summaries; wide sets of successful removals can
   therefore retain quadratic evidence metadata.
   Per-operation BDD limits in individual proof attempts are recoverable skips;
   shared phases and global exhaustion still stop admission. Skips keep their
   work charges, release temporary retained storage, and retry only after a
   relevant rewrite changes the graph or a dependent meaning. See
   [checker policies](../../docs/checker-policies.md#re-scoring) for the boundaries.
4. **Concrete replay.** `evaluate(present_inputs)` runs admitted components on a
   complete input snapshot (omitted tuples are absent; observations violating W are
   rejected). Facts are `Settled(true|false)` or `Blocked`; each established fact keeps
   its first grounded derivation; absence evidence names its provider component, the
   input snapshot or `NoPossibleProducer`.
5. **Symbolic meaning.** `symbolic` computes a condition per fact over the input
   variables; `check_at_most_one` gives scoped group results: `Proved`,
   `Overlap(condition)`, `Unsupported` or `Inconclusive { phase, resource }`.
6. **Verification.** `verify_at_most_one` turns overlaps into `Counterexample`s only
   after concrete replay confirms at least two distinct tuples. Findings carry the
   complete observation, the grounded proof DAG and the replay scope (`WholeProgram`,
   or `ConeOnly` when the whole program is not admitted).
7. **Certification.** `certify_observation` can establish one world's meaning in an
   otherwise unsupported program, upgrading `ConeOnly` replay for that observation.
   It still requires the whole program to complete. Emptiness and coverage searches
   skip worlds equivalent on all target and certification dependencies, preserving
   unresolved outcomes; see [checker policies](../../docs/checker-policies.md#certification-search).
8. **No-meaning findings.** For remaining negative-cycle components, completed
   equations identify permitted inputs with no consistent result. This is a sufficient
   failure check, not admission: a consistent equation solution does not establish
   meaning.

Reporting callers use the `*_checked` entry points: exhaustion before a report exists
is a top-level inconclusive outcome, never an empty success.

## Requests, keys and results

`PreparedCheck::admit_with_progress` accepts an optional invocation-local observer.
It reports rounds, stages, unresolved ground components with negation, affected
atoms, current component sizes and representative atoms/rules, and committed
rewrite counts. It also reports reused admission and exhaustion. Traversal and
upper-bound iteration updates are throttled; component upper-bound starts, stage
transitions and exhaustion are immediate. Callbacks perform no checking or key
projection, and are absent from semantic keys, receipts and retained admission.
Frontends resolve the representative's names and current source location. Counts
are snapshots, not percentages; completed admission can still leave unsupported
components. A single BDD operation has no inner progress heartbeat.

`OperationalLimits::progress` optionally carries an owned `CheckingProgress`
callback through direct and cached verification. It reports current targets and
operations, and limit/deadline failures at detection or recovery. Its scopes are
synchronous and invocation-local; use a separate observer for each concurrent run.
Private local runtimes retain their caller's target rather than exposing synthetic
arena identities. Notices and optional attribution recover from deadlines; ordinary
checking does not. No observer enters deterministic limits, query inputs, receipts
or cached semantic values. Frontends own delivery and source-name resolution.
Exhaustion is immediate; repetitive inner work is sampled. Callback delivery costs
wall time under the existing cooperative deadlines.

`CheckRequest::for_verification` builds a request from one IR verification: only its
selected assumptions constrain permitted worlds, and only its selected obligations
produce groups (including the compact domains for trivial groups). Preparation
rejects unknown obligation or verification keys and requests whose constraints or
obligations do not match their named verification. Input-only `at_most_one` contexts
retain their local checking path. General input/derived cardinality constraints
compute W independently during preparation, then use whole-program checking.
An empty W reports `inconsistent_assumptions` with no obligation results. Unknown W
is inconclusive. The IR classifies constraint cones before this evaluation; selected
cones requiring grounding must have no reachable negative cycle in the raw graph.

`validate_assumption_cones(corpus, domains, keys, limits)` is the program-level
declaration query, called before verification loops, including when none exist. It
uses relation-stratified cones immediately; others use fresh unrestricted grounding
with no obligation groups, followed by the existing graph's `blocked_by` and cycle
evidence. Results identify assumptions and cycle edges with semantic keys. It never
uses selected assumptions or admission, and never rejects an unrelated ground cycle.
An exhausted query retains established results and marks remaining declarations
inconclusive; cancellation aborts. The query recomputes per run, so facts, domains
and input eligibility cannot leave stale validation. Request preparation also checks
selected restrictions, including unnamed API requests, before computing W, returning
`InvalidAssumptionCone` with keyed evidence on failure. Program-level invalid
declarations do not prevent unrelated verifications from preparing.

Admission, rewrite proofs and no-meaning/unsupported analysis use that request's
constraints even when no obligations are selected. Unselected assumptions have no
effect. The transitional `all_obligations` constructor keeps existing callers working
with `verification: None`; unnamed requests may also select an obligation subset.
The public `GroundProgram::prepare*` entry points still cover all obligations.

For run-scoped fixed-fact evaluation, construct
`FixedPreparation::prepare(&corpus, &domains, &limits)` once, then use
`CheckRequest::prepare_with_fixed` for each verification. The artifact is bound to
that corpus snapshot, resolved domains and deterministic limits. It follows both
signs of relation dependencies, concretely evaluates only settled input-independent
atoms, and shares their original graph and derivations as evidence. Residual
admission and symbolic evaluation read those facts as constants. Blocked fixed
atoms remain residual. Selected-assumption validation still uses original ground
dependencies, as does the program-level validator.

The same artifact shares residual graphs, indexes and completed admission between
requests selecting the same restrictions. Each request still validates its named
verification and builds only its own obligation groups. Notices and diagnostic
example policies are never cached as part of that graph. An inconclusive attachment
or globally interrupted admission does not become a reusable completed result.
Completed admission with local proof skips is reusable, including its skip records
and receipts. `admission_skips()` exposes current failed attempts;
`admission_skips_for(component)` selects only targets in that component.
The source-bound graph
uses an immutable shared core, copied only when admission rewrites it.
`GroundKeyIndex` retains shared source schemas and declaration bindings plus the
request's groups. `PreparedCheck::key_view()` (or `GroundKeyIndex::view` for raw
programs) projects semantic atoms, instances, components and rewrite evidence on
demand from the current graph. Original and committed bodies remain distinct,
without keyed copies of either whole graph or an admission key refresh.
`original_content()` is an explicit full export for structural comparisons and the
optional relation-grounding cache; ordinary checking uses individual lookups.
`FixedPreparation::prepare_cached` exposes the owned fold kernel to session stores;
its `FixedInput`/`FixedValue` use semantic keys and rebind evidence to current IR.
The session owns Salsa and bounded retention, not the checker.

To share the program-level original check, use
`validate_assumption_cones_for_run(corpus, domains, keys, limits)` and then
`FixedPreparation::prepare_with_validation(&validated, limits)`.
`validated.result()` supplies the ordinary declaration diagnostics. The artifact's
private construction prevents a caller-edited diagnostic map from certifying a
request. It retains a compact relation-to-cycle index, with each keyed cycle once,
and releases the original graph. It also covers later unnamed API restrictions.
Without a supplied artifact, the first folded request needing ground validation
initializes the same query; later requests share it. A changed corpus, domain,
key table or deterministic limit cannot reuse that check. The original validation
has its own bounded allowance and `AssumptionValidation` receipt. Logical exhaustion
is shared as inconclusive within the run; cancellation and deadlines abort without
initializing the reusable result. Relation-stratified selections need no such query.

`atoms()`, `rules()`, `components()` and `dependencies()` include retained fixed
evidence; `fixed_size()` and `residual_size()` distinguish it from execution.
Presence replay can traverse fixed derivations; derived absence retains its
completed provider, not `NoPossibleProducer`. Successful folds carry a `FixedFacts`
receipt depended on by preparation; the owned path also records `FixedRuntime`
and `FixedBinding` transfer work. Fold exhaustion is explicit (`fixed facts`,
with subphase/resource); eligibility failures retain `input domains`. Cancellation
publishes no partial fold. The ordinary preparation API remains the unfolded
control. The `.den` frontends opt into folding; the test DSL's direct path is unchanged.

`ScopedResults.context` retains the request, including its optional `VerificationKey`.
Per-group and per-region outcomes use semantic identities (`GroupKey`, `ComponentKey`,
`AtomKey`), so results correspond across snapshots without arena IDs. Witness ordering
follows canonical `AtomKey` order, independent of declaration order.

Sessions share join plans and possible-tuple grounding independently of verification
selection. Group construction and admission run for the current request. Cached local
answers include their relevant constraints, input groups and obligation shape;
completion also includes any discharge-proof context. The result's request context
and counterexample replay are assembled fresh, so reused work cannot carry a previous
verification's identity into the current result.

Local query construction lazily indexes original producers and rewrite proofs by
head once per verification invocation. A worklist follows only the query's original
dependency closure, including dropped alternatives and upper-bound certificates;
each reached original and proof is projected once per query. The index borrows the
current graph and contains no semantic keys or owned evidence. It is released after
the local queries, never cached in a session or included in a receipt. Its physical
storage is proportional to original rules and proofs; it does not consume the BDD
condition allowance. `LocalMetrics.keys` includes the first query's index build.

## Coverage

`Verification.coverage` and `ScopedResults.coverage` contain per-obligation summaries:
examined groups, missing groups, unsupported groups, an optional inconclusive reason,
zero-group status and at most three replayed examples. Missing counts are exact only
when `complete()` is true. `proved()` requires complete checking and zero missing groups.
`ScopedResults::group` does not infer coverage from zero/one possible tuples: use the
coverage summary for its outcome. Existing uniqueness group identities are unchanged.

Coverage streams the Cartesian product of resolved grouping domains under a per-obligation
work allowance; retained examples are bounded independently. Empty grouping has one
group; an empty grouping-column domain has none. Counterexamples require replay-confirmed
absence of all possible members. When replay is blocked, observation certification may
establish absence or presence; uncertified worlds remain unsupported while bounded search
continues for a settled counterexample. A known-present tuple can prove coverage without
settling other producers. Selected assumptions must be consistent before coverage runs.

Coverage uses symbolic BDD fixed-point evaluation and searches the resulting absence
condition, then replays the concrete observation. Sessions reuse preparation but
recompute coverage evaluation and summaries each check; a separate coverage verdict cache
is deferred until measurements justify it. BDD is the only backend; the retirement and
reintroduction criteria are in [checker policies](../../docs/checker-policies.md#backend-retirement).

## Exactly one

An exactly-one obligation contributes its domain factors to coverage and its possible
multi-tuple groups to uniqueness. Both use the same selected input assumptions; neither
result is used as a restriction for the other. The existing evaluation, replay, budgets
and caches implement each part without a second authored obligation.

`ScopedResults.coverage` retains the coverage summary and `groups` retains uniqueness
results under the same obligation key. `KeyedGroups.kind` identifies the authored form;
`ScopedResults::group` queries uniqueness for exactly-one, not the combined obligation.
The overall verification proves only when both parts prove (and context-wide checks
succeed). An established failure survives exhaustion of the other part; both outcomes
remain available. The fresh global and cached local paths follow the same rule.

## Rewrites

Conservative rewrites remove a literal or rule only with a proof (for example, a
negation that is redundant under the other premises and W). They are reported as
rewrite findings with their coverage; they never authorize source edits.

`RewriteProof::candidate()` identifies the removed/changed rule. Its justification
is either a `SymbolicRewriteProof` with conditions and optional component bounds,
or a `StructuralProof` with shared settling/unfolding evidence. Use `symbolic()`
or `structural()` to inspect the corresponding certificate, and
`supporting_rules()` for current source placement. Structural removals use the
existing redundant-producer identity, never fabricated BDD conditions.

Concrete replay indexes discharge proofs by ground rule and literal occurrence.
The index stores only proof IDs alongside the committed rewrite state, including
proofs installed in reconstructed local runtimes. Removal proofs add no entries.
Cloning a snapshot preserves its lookup; transactional admission publishes the
updated graph and index together. This metadata changes neither semantic keys nor
logical work charges. Discharge applicability still builds and checks its condition
context under the caller's budget on each validation.

## Limits and cancellation

`Limits::profile` / `OperationalLimits::profile` optionally observe stage boundaries
and admission rounds. The default is disabled. Callbacks are observational and own
delivery; the checker performs no OS memory reads. The observer is excluded from
`DeterministicLimits`, receipts and cached values. BDD result counters count wrapped
result payload, not internal allocator traffic; retained snapshots deduplicate
shared `Condition` storage. See [memory profiling](../../docs/checker-policies.md#memory-profiling).

`Limits` bounds atoms, rule instances, dependencies, work, BDD storage and elapsed
time; exhaustion yields explicit inconclusive outcomes with phase and resource.
`CheckError`, `Inconclusive` and keyed `ResourceReason` carry `LimitDetails`: optional
subphase, effective limit and observed demand at the failed check. Observed demand
may include a rejected addition; an unknown solver count remains absent. Deadlines
carry the allowance in milliseconds, never elapsed timing. Input-domain preparation
preserves provider discovery/grounding/analysis/evaluation versus input enumeration.
Details do not charge work or alter verdicts; forwarded and cached reasons retain
them. Backend capacity or available work/storage can tighten the effective ceiling.
`Cancellation` is cooperative and checked at phase boundaries.

## Tests

```sh
just test-crate denotate-check
```

Tests include independent oracles: a Cartesian-grounded stable-model oracle for
rewrites and grounding, exhaustive small-world comparisons, and portable-condition
regression tests.

## Emptiness

`empty` has one ungrouped `EmptinessReport` per selected obligation (keyed as
`EmptinessResult` in `ScopedResults.emptiness`). `examples` defaults to at most three
distinct replayed present tuples, each with its own observation.
`PreparedCheck::with_emptiness_examples(EmptinessExamples::Limited(n))` selects a
positive sample size; `EmptinessExamples::All` retains every confirmed tuple.
This invocation-level reporting choice is outside `CheckRequest`, semantic limits
and cached inputs. It changes neither candidate enumeration nor deterministic
charges. Extra examples consume memory and receive independent post-check attribution
allowances. All modes keep semantic-key order and exact/lower-bound count semantics.
`unresolved` and `inconclusive` keep unknown
worlds and resource exhaustion visible independently of a known failure. `proved()`
requires complete analysis and zero present tuples. The BDD checks settled presence conditions;
blocked facts require world replay/certification, with enumeration and evidence charged
to the obligation's allowance. Sessions reuse preparation and recompute these verdicts.

## Advisory condition queries

`Corpus::notice_varies_in` declares a zero-arity condition and optional enclosing
scope; `verification_with_notices_in` selects notices. `CheckRequest::for_verification`
validates and retains that selection. `ScopedResults.notices` returns keyed results.
`GroundProgram::analyze_condition` is the corresponding low-level query on a prepared,
admitted program: impossible, always true, varying, parent unreachable, or unknown.
The query uses W, symbolic settled conditions and independent concrete replays; it
never assumes the conclusion. Both sides of varying have their own full observation.
Unknown results retain the cause: `ConditionAnalysis.blocked_by` records the blocking
components returned by symbolic meaning; `NoticeResult.blockers` projects these to
semantic component and cycle-rule keys for presentation. Deadline reasons retain the
phase. Collecting this evidence does not perform additional checking or charge budgets.

Each selected notice runs after ordinary checking with a fresh deterministic and
operational allowance. Its receipts use `QueryKey::Notice`; a deadline is unknown
without a semantic receipt, while cancellation aborts. Sessions currently recompute
these queries. They do not affect obligation verdicts/completeness. No implicit
notice selection is added to the legacy `all_obligations` constructor.
