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
   Admission first targets negative components and their blocked providers
   (`relevant`), retaining their complete support. Then `downstream` handles
   still-blocked downstream removals and assumption-dependent input-negation
   warnings on settled heads, including programs with no cycles. Structural
   worklists, symbolic evaluation and summaries are scoped to the current targets'
   providers; input variables/W and transactional graph maintenance remain shared.
   Each round first performs structural truth/false propagation, dead-rule removal
   and bounded signed-body subsumption through single-producer positive chains.
   Removals target blocked regions; already settled rules supply truth/evidence.
   Structural changes commit before symbolic evaluation, using the same atomic
   graph rebuild. They require no BDD operations. Each settled snapshot then proves
   redundant producer removals from independent
   exact coverage. A nonempty removal batch is committed and the components rebuilt
   before another snapshot. When cheap removals have no batch, lower guarantees
   from exact producers strengthen descending cycle upper bounds. A non-exact
   producer is removed if its body's upper bound implies the independent exact
   head cover under W. Exact producers are retained; recursive lower coverage is
   excluded. These bounds preserve supported-model possibilities and never settle
   executable atoms. Only a snapshot with no removals proceeds to negation
   discharge. If discharge also has no batch, guarded settlement can replace a
   cyclic signed premise by a Boolean expression over globally settled atoms,
   valid under the reading rule's retained guard. Rank-ordered marks use bounds
   computed with that reading producer relaxed to its guard; it cannot justify
   itself. Bounds are restricted to G ∧ W and the premise's live dependency cone,
   in a separate `GuardedBounds` certificate. Preprocessing is lazy and charged;
   guards with smaller estimates run first. A single snapshot-local entry reuses
   only identical computations, including failures, never a failure under a
   broader guard. Conditions and cache metadata are charged and released.
   Temporary cones borrow already-accounted round summaries and store explicit
   live/dead flags. They retain no masked producer conditions: bounds and settlement
   restrict contributions transiently before accumulation. Successful proofs own
   just their referenced snapshot summaries and bound values, with conservative
   ownership charges after the round/cache is dropped. Failed preparation reports
   partial cone counts and existing/added storage before releasing its values.
   One replacement per component commits atomically. Later exhaustion
   preserves earlier committed batches.
   Within a snapshot, exact-producer coverage is computed lazily per head, reused
   by its non-exact candidates, and removed from the cache after the last candidate.
   Retained unions count against the existing condition-node limit. Proofs still
   keep their covering producer summaries; wide sets of successful removals can
   therefore retain quadratic evidence metadata.
   Per-operation BDD limits in individual proof attempts are recoverable skips.
   Temporary bounds/cone storage exhaustion is also a skip after releasing partial
   values; proof/shared storage failures still stop. Limits are unchanged;
   shared phases and global exhaustion stop that phase. Phase B records
   `GroundProgram::downstream_incomplete()` and `ScopedResults::downstream_incomplete`
   separately from `admission_limit()`. This advisory result preserves phase A's
   admitted/unsupported classifications, survives same-context reuse with its
   receipt, and does not change exit codes. Deadlines/cancellation still abort.
   Downstream producers that become exact before phase B may lose their old rewrite
   warnings; retaining every warning is not part of this ordering policy. Skips keep their
   work charges, release temporary retained storage, and retry only after a
   relevant rewrite changes their inputs. Coverage and removal compare exact
   producers and settled premises, including edits to settled premise cones;
   blocked-only dependency changes do not retry them. Bounds and discharge retain
   conservative graph invalidation, as do bound-removal attempts: a blocked-only
   dependency change can tighten a bound. Retry comparison is part of the atomic commit.
   Completed negative removal, bound-removal and discharge attempts use the same
   invalidation, within this admission invocation. Their cache contains identities
   and metadata only, and is consulted before computing coverage or bounds used
   solely by cached consumers. Negatives are not skips and never mark a region
   inconclusive. Symbolic results, summaries and successful bounds are rebuilt
   each round. Progress reports per-round attempts run/reused, outcomes, retry
   causes and elapsed time, separately from symbolic evaluation and summaries.
   See
   [checker policies](../../docs/checker-policies.md#re-scoring) for the boundaries.
4. **Concrete replay.** `evaluate(present_inputs)` runs admitted components on a
   complete input snapshot (omitted tuples are absent; observations violating W are
   rejected). Facts are `Settled(true|false)` or `Blocked`; each established fact keeps
   its first grounded derivation; absence evidence names its provider component, the
   input snapshot or `NoPossibleProducer`. Attached settled expressions are
   evaluated against the same replay; `PremiseEvidence::Replaced` refers to the
   original occurrence and certificate. Consulted expression leaves supply ordinary
   presence/absence evidence. Observation certification can prune a false composite
   condition and records that condition and its settled leaves explicitly.
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

Guarded settlement uses bounded `SettledExpression` trees on `GroundRule` and keyed
`GroundInstance` values. Graph edges, symbolic meaning, completion, replay and local
reconstruction all read their leaves. Source identities remain the original rule
and replaced occurrence; `KeyedRewriteKind::GuardedSettlement` distinguishes the new
internal proof. The default `guarded-settlement` warning is advisory, with direct
support and the retained guard; full evidence shows rank-ordered settlement and
relaxed bounds. See [the soundness argument](../../docs/decisions.md#meaning-and-checking)
and [cutoffs](../../docs/checker-policies.md#guarded-settlement).

Guarded settlement can infer a stronger guard from one hop of producer summaries:
negative unresolved premises exclude exact producer guards; positive ones require
some producer's settled guard. `ImpliedGuardProof` owns those source snapshots,
including producers outside the replaced premise's cone. The guard remains in the
attached executable expression and participates in key projection and local query
dependencies. Discovery is lazy and bounded; a local failure uses the original
guard and is reported as an `implied-guard` attempt, without making that fallback
inconclusive. Finding identities and the earlier admission passes are unchanged.

Structural rewrite proofs expose direct settling/unfolding support through
`direct_rules` and accurate absence explanations through `settlement`. Internal
rewrite keys use that direct view. `supporting_rules` explicitly expands the full
retained certificate for detailed evidence; ordinary presentation does not call it.
This projection does not narrow the original dependency closure in local query
inputs, so transitive edits still invalidate reuse. Presentation owns display caps;
neither proof coverage nor checker limits change.

`PreparedCheck::admit_with_progress` accepts an optional invocation-local observer.
It reports relevant/downstream phases, rounds, stages, unresolved ground components with negation, affected
atoms, current component sizes and representative atoms/rules, and committed
rewrite counts. It also reports reused admission and exhaustion. Traversal and
upper-bound iteration updates are throttled; component upper-bound starts, stage
transitions and exhaustion are immediate. Callbacks perform no checking or key
projection, and are absent from semantic keys, receipts and retained admission.
Frontends resolve the representative's names and current source location. Counts
are snapshots, not percentages; completed admission can still leave unsupported
components or an explicit downstream incomplete marker. A single BDD operation
has no inner progress heartbeat.

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
`BackendIdentity::bdd_with_order(InputOrder::{Key, ReverseKey, Structural})` selects
an experimental variable layout; `bdd()` still means key order. Preparation chooses
one map after grounding and copies it to the assumption-specialized view before W.
Structural placement uses only dependencies and selected constraints, with charged
cutoffs that fall back to key order. `GroundProgram::input_order_report()` describes
the requested/effective order and any fallback; `ordered_input_atoms()` exposes the
map. Order participates in shared-context and local-query reuse; local inputs also
carry the actual projected sequence. See the [policy](../../docs/checker-policies.md#diagnostic-input-ordering)
for the deterministic heuristic and its bounds.
An empty W reports `inconsistent_assumptions` with no obligation results. Unknown W
is inconclusive. The IR classifies constraint cones before this evaluation; selected
cones requiring grounding must have no reachable negative cycle after one
specialization by independently settled fixed truth.

`validate_selected_assumption_cones_using(corpus, domains, keys, requests, limits, factory)`
is the run-level declaration query. It takes the executed requests before their
verification loops, selects declarations by semantic key and uses relation-stratified
cones immediately. Unselected cones needing grounding return `NotSelected`; they
neither call the factory nor make the run incomplete. `is_valid()` still means every
declaration was validated; `has_failures()` tests for invalid/inconclusive results
that affect the run. `selected_failure` rejects an attempt to use a deferred result
for a newly selected request. Selected cones needing grounding prepare the fixed fold and one
residual graph with no obligation groups. A separate view removes dead instances
and satisfied fixed premises, then supplies `blocked_by` and cycle evidence.
Blocked fixed atoms never become false, and newly exposed truth does not trigger
another fold. W uses that same specialized meaning. Results identify assumptions and cycle edges with semantic keys. It never
uses selected assumptions or admission, and never rejects an unrelated ground cycle.
An exhausted query retains established results and marks remaining selected declarations
inconclusive; unselected ones stay deferred and cancellation aborts. The query recomputes per run, so facts, domains
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
atoms remain residual. Assumption validation and W use a specialized view of those
residual dependencies; ordinary admission keeps the original rules and evidence.

The same artifact shares residual graphs, indexes and completed admission between
requests selecting the same restrictions. Each request still validates its named
verification and builds only its own obligation groups. Notices and diagnostic
example policies are never cached as part of that graph. An inconclusive attachment
or globally interrupted admission does not become a reusable completed result.
Completed admission with local proof skips is reusable, including its skip records
and receipts. `admission_skips()` exposes current failed attempts;
`admission_skips_for(component)` selects only targets in that component.
Source-bound graphs use immutable shared cores. Specializing an assumption view,
attaching a different input context or committing admission rewrites detaches a core
on mutation; unchanged snapshots share it.
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

To share selected validation with verification preparation, use
`validate_selected_assumption_cones_using(..., requests, limits, factory)` and then
`FixedPreparation::prepare_with_validation(&validated, limits)`.
`validate_assumption_cones`, `validate_assumption_cones_for_run` and
`validate_assumption_cones_using` retain explicit all-declaration validation for
authoring tools. The factory runs only when a cone in the validation selection needs grounding;
`prepare_cached_with_validation` reuses that bound fold instead of transferring it
again. `validated.result()` supplies declaration diagnostics. The private artifact
cannot be fabricated from a caller-edited diagnostic map. It retains fixed evidence,
the original residual and its specialized view, and a compact relation-to-cycle
index with each keyed cycle once. Original rules/instances stay intact for ordinary
admission, provenance and rewrite warnings. No separate whole-program grounding
survives or is rebuilt by subsequent requests.

Without a supplied artifact, the first request needing ground validation initializes
the same query, including unnamed restrictions and optional grounding-cache calls.
These requests use fixed preparation rather than relation-SCC cache assembly. Other
direct requests retain their existing unfolded path. A changed corpus, domain,
key table or deterministic limit cannot reuse the artifact. Residual preparation,
specialization and cycle indexing have one bounded allowance and
`AssumptionValidation` receipt, depending on the separately charged `FixedFacts`.
Request attachment and W have the preparation allowance. Logical exhaustion is
shared as inconclusive within the run; cancellation and deadlines install no partial
reusable preparation. Relation-stratified validation needs no fold or residual query.

`atoms()`, `rules()`, `components()` and `dependencies()` include retained fixed
evidence; `fixed_size()` and `residual_size()` distinguish it from execution.
Presence replay can traverse fixed derivations; derived absence retains its
completed provider, not `NoPossibleProducer`. Successful folds carry a `FixedFacts`
receipt depended on by preparation; the owned path also records `FixedRuntime`
and `FixedBinding` transfer work. Fold exhaustion is explicit (`fixed facts`,
with subphase/resource); eligibility failures retain `input domains`. Cancellation
publishes no partial fold. The ordinary preparation API remains an unfolded
control for relation-stratified selections; cyclic assumption cones require the same
fixed specialization on every path. The test DSL's direct path is unchanged.

`ScopedResults.context` retains the request, including its optional `VerificationKey`.
Per-group and per-region outcomes use semantic identities (`GroupKey`, `ComponentKey`,
`AtomKey`), so results correspond across snapshots without arena IDs. Witness ordering
follows the configured variable map (semantic `AtomKey` order by default),
independent of arena allocation. Witness choices are not semantic goldens.

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
is a `SymbolicRewriteProof` with conditions and optional component bounds,
a `StructuralProof` with shared settling/unfolding evidence, or a
`BoundRemovalProof` with the candidate body's upper bound and the exact-cover
certificate. Use `symbolic()`, `structural()` or `bound_removal()` to inspect the
corresponding certificate. `direct_rules()` supplies ordinary source placement;
`supporting_rules()` requests full support. Structural and bound removals use the
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
