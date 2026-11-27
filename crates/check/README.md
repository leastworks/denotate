# denotate-check

The finite relational checker. It grounds a `Corpus` over explicit finite domains,
checks admissibility, replays concrete input worlds, and proves or refutes
`at_most_one`, `at_least_one`, `exactly_one` and `empty` obligations symbolically (BDD), returning
only replayed counterexamples. Runtime dependencies: `denotate-ir`, pinned
`biodivine-lib-bdd`.

For experimental resumption, `PreparedCheck::admit_until_round` optionally stops
after a complete admission round and returns `StoppedAfterRound`. Its borrowed
`AdmissionDumpEvent::Graph` includes the last committed graph and round, even on
interruption. The stop is independent of progress delivery and cancellation, bypasses
completed-admission reuse, and cannot populate that cache. Default admission entry
points retain their existing behavior. `residual_rules`, `original_residual_rules`
and `fixed_true_atoms` expose the executable graph and independent assumption
source without traversing fixed derivation evidence. Serialization belongs to
[`ir-text`](../ir-text/README.md#committed-program-experiments).

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
   group. `admit` applies justified rewrites. Diagnostic structural ordering packs
   declared input cardinality groups into semantic-key-ordered blocks before U/W
   construction; selected assumptions remain weighted preferences. Its report uses
   `EffectiveInputOrder::GroupedKey` on a placement-allowance fallback and counts
   scattered declared groups in explicit key/reverse-key modes. See the
   [ordering policy](../../docs/checker-policies.md#diagnostic-input-ordering).
3. **Admissibility.** Positive cycles are admitted. A negative edge inside an SCC blocks
   that component and its dependents unless a rewrite proves the negation redundant
   under W. Blocked regions are reported (`Unsupported`), never treated as false.
   Admission first targets negative components and their blocked providers
   (`relevant`), retaining their complete support. Then `downstream` handles
   still-blocked downstream removals and assumption-dependent input-negation
   warnings on settled heads, including programs with no cycles. Structural
   worklists and symbolic evaluation cover the current targets' providers; input
   variables/W and transactional graph maintenance remain shared. Summaries retain
   complete producer sets for target components and one-hop support used by cyclic
   implied guards. Symbolic intermediates outside those readers are released after
   their last consuming component completes; replacement-expression leaves count as
   readers. Released conditions cannot silently read as false. Summary construction
   is transactional per producer head: local BDD/storage failure discards the whole
   group, skips every dependent component, and preserves independent attempts and
   committed proofs. `summary-storage` records the cause and survives session reuse.
   Each round first performs structural truth/false propagation, dead-rule removal
   and bounded signed-body subsumption through single-producer positive chains.
   Removals target blocked regions; already settled rules supply truth/evidence.
   Structural changes commit before symbolic evaluation, using the same atomic
   graph rebuild. They require no BDD operations. Each settled snapshot then proves
   redundant producer removals from independent
   exact coverage. Removals, bound removals and discharge visit components in
   provider-first target levels, then by size. Each successful component batch
   commits immediately; the schedule is rebuilt with the graph. All cheap removals
   must have no batch before bounds begin. Next, structural split search tries the
   original negative-cycle component under W: split on settled atoms, prune dead
   producers, and evaluate every acyclic leaf topologically. Live unresolved
   external premises fail the attempt. One shared joint certificate installs all
   internal replacements atomically, including constants and multiple occurrences;
   no bounds are computed. `Limits::max_structural_split_depth`,
   `max_structural_split_leaves` and `max_structural_split_work` bound this optional
   attempt, including BDD preflight work. A local cutoff or partial/oversized
   certificate falls back; global work/deadlines/cancellation still stop admission.
   `max_structural_split_scoring_work` bounds further scoring per node, cooperatively
   between complete scores, keeping the best improving choice. It reserves no leaf
   work. The chosen cones/SCC scores can be reused under a small charged reservation;
   the best and in-flight pairs share one cap, and deeper scoring evicts waiting siblings.
   Storage pressure retries without that reservation, with work still charged.
   Joint expression DAGs retain sharing through semantic projection/rebinding;
   equal branches and direct complementary terms simplify structurally during
   interning. No domain-relative equivalence query is added. Profiling optionally
   reports per-batch replacement DAG size and unrestricted versus W-restricted
   BDD sizes, with independent bounded inspection and explicit incomplete results.
   Construction uses charged work/storage and separate safety caps rather than
   the single-premise expression caps. Unchanged cutoffs are skipped within the
   admission; supporting-provider changes invalidate them.
   Negations proved always true under their settled guard keep redundant-negation
   warnings and safe frontend edits, independently of which proof path established
   them. Genuine expression replacements remain equivalence warnings. If that
   search has no batch, lower guarantees
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
   in a separate `GuardedBounds` certificate. An optional deadness pass first
   propagates impossible guards through positive chains and negative premises
   guaranteed by exact producers. Unseeded cycles remain possible; the reading
   producer stays relaxed. Rebuilt cones retain transitive pruning sources as
   separate owned evidence. Optional size/BDD/storage failure uses the old cone;
   global work, deadlines and cancellation propagate. Preprocessing is lazy and charged;
   components take upstream-first turns of at most four bounds candidates, with
   size/order ties. Within each component the existing guard/cone ranking and
   lookahead apply. Waiting queues keep their ranking metadata; storage pressure
   can release it and saved inferred guards without losing candidates. Guards are
   rediscovered when those candidates resume. A lone component
   continues without a switch. Bounds reuse and local skips consume a turn slot,
   while preparation and cached-negative lookups do not. A single attempt can
   still spend the global allowance; there is no within-attempt yield.
   A single snapshot-local entry reuses
   only identical computations, including failures, never a failure under a
   broader guard. Conditions and cache metadata are charged and released.
   Candidate preparation shares liveness and exact-guarantee tests for the most
   recent domain in the snapshot, with exact-producer membership checked before
   reuse. Its bounded, charged cache yields on storage pressure. Relaxation,
   reachability and propagated deadness remain candidate-specific.
   Temporary cones borrow already-accounted round summaries and store explicit
   live/dead flags. They retain no masked producer conditions: bounds and settlement
   restrict contributions transiently before accumulation. Successful proofs own
   just their referenced snapshot summaries and bound values, with conservative
   ownership charges after the round/cache is dropped. Failed preparation reports
   partial cone counts and existing/added storage before releasing its values.
   Replacements whose complete dependencies are mutually untouched share an atomic
   batch, with one replacement per rule. A nonempty guarded batch commits before
   work starts on another component. Dependencies include dead producers,
   transitive pruning sources and implied guards. Prepared descriptors and ranking
   sizes can survive a round when these inputs and G ∧ W stay unchanged; current
   summaries and component IDs are rebound. Descriptors and retry footprints are
   charged to existing storage/work allowances and released at admission end;
   bounds remain snapshot-local. Changed inputs invalidate guarded attempts,
   while unrelated attempts survive. Whole-component bounds retry when their
   component changes. Later exhaustion preserves earlier committed batches.
   Within a snapshot, exact-producer coverage is computed lazily per head, reused
   by its non-exact candidates, and removed from the cache after the last candidate.
   Retained unions count against the existing condition-node limit. Proofs still
   keep their covering producer summaries; wide sets of successful removals can
   therefore retain quadratic evidence metadata.
   Per-operation BDD limits in individual proof attempts are recoverable skips.
   Temporary bounds/cone storage exhaustion is also a skip after releasing partial
   values. Escaping storage failures in a component's removal/bound-removal/discharge
   pass discard that component's pending proofs and temporary conditions, then
   restore their accounting. Shared summaries and earlier committed proofs stay
   charged. The component is skipped until a rewrite changes its dependency cone;
   the skip is visible as `component-storage`. Guarded certificate retention also
   recovers per attempt, preserving earlier certificates in its independent batch.
   Shared storage failures still stop. Limits are unchanged;
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
   variables. Positive recursive components use dependency-driven sparse rounds:
   evaluate every producer initially, then only readers of changed premises,
   in the existing producer order. This computes the same least fixpoint; dense
   growth can still require many evaluations. Scheduling metadata is charged and
   falls back to full scans if its storage is unavailable or needed by conditions.
   `check_at_most_one` gives scoped group results: `Proved`,
   `Overlap(condition)`, `Unsupported` or `Inconclusive { phase, resource }`.
   An individual atom's BDD task/node or retained-condition limit makes its exact
   condition unknown, rather than ending admission or independent checking.
   Unknown propagates through readers unless a false conjunct or true alternative
   decides the expression. A positive recursive component restarts from bottom
   after a head exhausts, treating that head as opaque; partial approximations
   never become exact facts. `unknown_atoms()` and verification results retain
   the originating atom and resource cause. Local session values use semantic keys
   and retry after changed producers or limits. Shared context setup, total work,
   deadlines and cancellation retain their existing failure boundaries.
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
A bounded lookahead ranks prepared cones before attempting their bounds, deferring
full and nearly full cones. Waiting candidates retain only size metadata; their
cones are rebound from unchanged prepared descriptors when available, while
guards are rediscovered when selected. An all-deferred window can extend within a
deterministic charged-work allowance per snapshot; it tries the first useful cone
found, or the best deferred one when the allowance is spent. Optional descriptors
and ranking yield under preparation storage pressure. This scheduling allowance
never becomes a checker-limit finding or failed-proof cache entry.
The [checker policies](../../docs/checker-policies.md#guarded-settlement) describe
its provisional window, threshold and progress fields.

If ordinary guarded bounds fail locally or settlement is negative, a bounded case
search can split the effective domain on globally settled input or derived atoms.
An executable-cone SCC score chooses useful splits; it is never proof evidence.
The earlier component-wide structural search uses the same score and cutoffs, but
its `GuardedCertificate::Joint` shares the original producers and an `Acyclic` leaf
certificate with every atom's value and deadness reasons. All occurrence proofs
must commit together. It uses no candidate relaxation or bounds. See the
[joint proof decision](../../docs/decisions.md) and
[structural-split policies](../../docs/checker-policies.md#structural-splits).
Each live branch obtains fresh candidate-relaxed bounds and a non-circular
certificate, including constant leaves justified by false upper bounds or
independently exact producers. Only a complete tree becomes a replacement, with
the effective guard retained. `GuardedCertificate` records leaves, splits and
empty domains; execution still consumes the combined `SettledExpression`.
Branch caches are deliberately absent. Complete branch dependencies participate
in batching, original evidence closure and local-query invalidation. Progress and
full warning evidence expose the split and its branches. See the
[case-split policies](../../docs/checker-policies.md#case-splits).

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

Requests carry authored `Semantics` and an optional semantic-keyed hypothesis.
Current BDD and SAT checking, sessions and planning support only stable semantics
without a hypothesis. `require_stable` / `require_stable_verification` reject other
configurations before preparation; changing request fields cannot bypass the named
declaration. `no_rejections` has no cardinality group and is not checked yet.

`CheckRequest::for_verification` builds a request from one IR verification: only its
selected assumptions constrain permitted worlds, and only its selected obligations
produce groups (including the compact domains for trivial groups). Preparation
rejects unknown obligation or verification keys and requests whose constraints or
obligations do not match their named verification. Input-only `at_most_one` contexts without input cardinality declarations
retain their local checking path. General input/derived cardinality constraints
compute W independently during preparation, then use whole-program checking.
Only the selected restriction relations' dependency cones are symbolically
evaluated to build W, using the independent specialized graph where needed. The
full input universe and chosen order are retained, including inputs outside those
cones. Empty coverage groups still constrain W. This does not narrow subsequent
admission, notices or other program-wide reports.
`BackendIdentity::bdd_with_order(InputOrder::{Key, ReverseKey, Structural})` selects
an experimental variable layout; `bdd()` still means key order. Preparation chooses
one map after grounding and copies it to the assumption-specialized view before W.
Structural placement uses dependencies, declared cardinality blocks and selected
constraints. Selected uniqueness groups are weighted preferences; declared groups
are contiguous blocks. Assumption enforcement is independent of placement.
Configurable `max_input_order_entries` and `max_input_order_work` allowances fall
back to grouped-key order when declared blocks exist, and key order otherwise;
global exhaustion still stops preparation. The mandatory block baseline remains
with zero optional allowance. Support vectors and repeated unions are shared while hyperedge
weights are preserved. Entry accounting bounds peak retained metadata; cumulative
work remains charged to the preparation budget. The early `CheckingTarget::InputOrder` event reports the chosen
order and cutoff demand before assumption construction.
`GroundProgram::input_order_report()` describes the requested/effective order and any fallback; `ordered_input_atoms()` exposes the
map. Order participates in shared-context and local-query reuse; local inputs also
carry the actual projected sequence. See the [policy](../../docs/checker-policies.md#diagnostic-input-ordering)
for the deterministic heuristic and its bounds.

Opt-in verification-only symbolic evaluation (`CheckRequest::checking_within_w`,
default false) stores exact `c ∧ W` conditions: truth is
W, false is false, negation is `W ∧ ¬c`, and recursive convergence compares these
masked conditions. This is a separate const-generic `SymbolicMeaning<true>` type;
public symbolic entry points and admission/proof consumers use the default type,
exact throughout the declared legal universe U. Inputs, fixed facts and executable replacement expressions follow
the same checking algebra. A true-throughout-W alternative still masks an unknown
one; unresolved atoms are never interpreted as absent.

Whole-program verification, notices, and the local path's whole-program
coverage/emptiness pass use this mode when enabled. The default retains the raw
evaluation path. The option participates in checking query identity, but not
shared preparation, W or admission identity. Cached local uniqueness/no-meaning
evaluation, its exported conditions and import boundary remain unrestricted.
Assumption construction and admission are unchanged. Masking can enlarge small
conditions by carrying unrelated constraints; existing limits still apply, and
an exhausted computation remains inconclusive.

An empty U reports `empty_input_universe`; otherwise an empty W reports `inconsistent_assumptions` with no obligation results. Unknown W
is inconclusive. The IR classifies constraint cones before this evaluation; selected
cones requiring grounding must have no reachable negative cycle after independent ground-atom propagation to a fixpoint.

`validate_selected_assumption_cones_using(corpus, domains, keys, requests, limits, factory)`
is the run-level declaration query. It takes the executed requests before their
verification loops, selects declarations by semantic key and uses relation-stratified
cones immediately. Unselected cones needing grounding return `NotSelected`; they
neither call the factory nor make the run incomplete. `is_valid()` still means every
declaration was validated; `has_failures()` tests for invalid/inconclusive results
that affect the run. `selected_failure` rejects an attempt to use a deferred result
for a newly selected request. Selected cones needing grounding prepare the fixed fold and one
residual graph with no obligation groups. A separate view propagates independently settled ground atoms: one satisfied
producer proves true; all producers independently dead (or none) proves false.
New truth triggers further propagation before rebuilding `blocked_by` and cycle
evidence. Structural blocking alone proves neither value. No new unfounded-set
analysis is performed. W uses that same specialized meaning. Results identify assumptions and cycle edges with semantic keys. It never
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
propagation and cycle indexing have separate bounded allowances and receipts:
`ResidualPreparation` depends on `FixedFacts`, `SettledAtoms` on the residual, and
`AssumptionValidation` on settlement.
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

## Diagnostic SAT probe

`PreparedCheck::admit_with_probes` can run component uniqueness/existence probes
on actual admission snapshots, after structural reductions and producer removals,
in provider-first order. A borrowed `SatProbeObserver` receives a starting event
and a `SatProbeReport` with the current graph, revision and round. Settled providers,
replacement expressions and W are read from existing exact conditions; read-only
BDD encoding avoids reconstructing their upstream rules. An unresolved external
provider gives `unknown`; later snapshots can use it once it settles.

SAT returns a reduct-verified pair; UNSAT establishes at most one stable meaning.
After UNSAT, a separate `SatExistenceReport` reports `every-world`, `no-meaning`
with an input world, `inconsistent-assumptions`, or `unknown`. Both questions apply
only to the target under its exact settled boundary and W. Diagnostics never
change admission, normal results or caches. The CLI opts in with `--sat-probe`;
no probe runs by default. Reused admission emits no queries. Each reached snapshot
has independent diagnostic allowances; all diagnostic time, including delivery,
is excluded from the admission deadline. Cancellation stays live.

`PreparedCheck::sat_probe(component, probe_limits, operations)` remains available
for explicit pre-admission whole-cone comparisons. It does not accept rewritten
graphs. The CLI uses the compact admission path above.

The probe encodes Clark completion using batsat, refines unfounded candidates with
external-support clauses and independently evaluates each reduct by a positive
worklist. Exact conditions include the ordinary evaluator's least meaning of settled
positive recursion; unresolved upstream components produce unknown. CNF and cone size/work
use separate invocations of the existing limits; time and refinement limits are
probe-specific, independently for uniqueness and existence. Cancellation propagates.
Existence alternates a W-only world query with a pinned-input stable-model query.
Their encodings share one SAT engine with a selector: target equations cannot
exclude worlds from the first query. Stable models cover generalized input cubes;
these preserve true rule bodies and a false premise for every false body, including
negative and alternative producers. See the [soundness argument](../../docs/decisions.md#meaning-and-checking)
and [policy](../../docs/checker-policies.md#diagnostic-sat-probe)
for the precise meaning, bounds and reporting contract.

`PreparedCheck::admit_with_candidate_probe` optionally diagnoses guarded-settlement
candidates on their actual admission snapshots. `CandidateProbeLimits` supplies
one aggregate allowance per invocation; `AdmissionProgress` delivers
`candidate_probe` and `candidate_probe_counts` only on diagnostic events. Reports
are not cached; a reused admission emits its usual reuse event without queries.
The two supported-model copies disagree on the target premise, with the reading
producer's contribution free under its effective guard. Settled providers and W
are encoded from their exact existing conditions. No stability refinement runs in
the unresolved cone. A verified pair rules out this kind of certificate on this
snapshot; UNSAT only means not ruled out. Neither answer affects admission.
Probe time is excluded from the checker deadline, and cancellation still applies.
See the [candidate policy](../../docs/checker-policies.md#guarded-candidate-filter).

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
is deferred until measurements justify it. BDD remains the default backend; the retirement and
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

`Profile::observe_conditions` opts into a separate detailed callback before a run.
It observes generic ground atoms, retained condition sizes, assumption checkpoints,
input order and failed Boolean operations. Atom handles belong to that invocation;
drivers resolve names/semantic identities before persisting records. Disabled
observation does no per-producer atom cloning or locking. The callback performs
no additional Boolean evaluation or logical charging; elapsed-time overhead can
still affect deadlines. It is intended for diagnosis, not cached query results.

`Limits` bounds atoms, rule instances, dependencies, work, BDD storage and elapsed
time; exhaustion yields explicit inconclusive outcomes with phase and resource.
`CheckError`, `Inconclusive` and keyed `ResourceReason` carry `LimitDetails`: optional
subphase, effective limit and observed demand at the failed check. Observed demand
may include a rejected addition; an unknown solver count remains absent. Deadlines
carry the allowance in milliseconds, never elapsed timing. Input-domain preparation
preserves provider discovery/grounding/analysis/evaluation versus input enumeration.
Details do not charge work or alter verdicts; forwarded and cached reasons retain
them. Backend capacity or available work/storage can tighten the effective ceiling.
Cancellation is checked at every charge and explicit boundary. Deadline clock
reads occur on the first charge, then every 256 charges; explicit `Budget::check`
and zero-work charges always read it immediately. At most 255 charge opportunities
skip the clock. This bounds polling work, not elapsed response time: an operation
between checks can still run for a long time. Deterministic work charges are unchanged.

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

## Admission diagnostic snapshots

`PreparedCheck::admit_with_diagnostics` optionally delivers borrowed `AdmissionDump`
records synchronously: actual guarded cones, signed guards, implied-guard sources,
pruning evidence and outcomes, plus the last committed graph on completion, reuse
or interruption. No earlier attempt is reconstructed from the final graph. The
observer owns bounded formatting and delivery; the checker performs no IO and
retains no diagnostic state in sessions. Its delivery time is excluded from the
admission deadline. Reused admission emits its graph and no invented attempts.
The CLI [component-dump guide](../ir-text/examples/check/COMPONENT-DUMP.md) describes
the bounded writer and its independent failure reporting.

### Declared input universe

`Corpus::constrain_input` attaches one `InputCardinality` (at-most-one or exactly-one)
to an input. Preparation groups eligible tuples by their declared columns, after
applying resolved domains and fixed `within` facts. It creates no group without
candidates, including for `group_by: ()`. The current disjoint input declarations
always permit an assignment; `input_universe_is_empty()` remains a defensive API
check, and the existing empty-universe status remains reserved. Selected assumptions
can still be inconsistent. Concrete observations must satisfy both U and W. Coverage
obligations and named assumptions still enumerate Cartesian grouping domains.

`ConditionContext` installs the universe before selected restrictions. Default
symbolic evaluation uses one fixed mask per component: the conjunction of declared
group factors intersecting its closed structural input support. Child conditions
are intersected with the consumer mask; truth is that mask and negation subtracts
from it. Raw difference is exact convergence within the mask. Final semantic
queries still use full W. Selected assumptions are not component masks. The
verification-only `checking_within_w` option instead keeps its full-W algebra.
Proof queries, completion, notices and SAT probes share the same legal-world
contract. Programs with declarations temporarily use global verification rather
than the local cache's at-most-one-only absent extension.

Opt-in `Profile::observe_conditions` includes in-progress recursive-component
snapshots: rounds, producer visits/evaluations, changed heads, relation totals,
largest current conditions, retained array storage and cumulative result traffic.
It also supplies a bounded graph-only cycle sample. These observations are partial
approximations, not settled facts, and never enter cached semantic results.
The CLI projects them with `--profile-memory FILE --profile-conditions`.

## CNF size experiment

`cnf_measurement::Measurement` folds fixed facts and grounds the whole residual
program without W, admission, or input-dependent BDD evaluation. It measures
completion plus declared input cardinality U; selected assumptions and obligations
are not encoded. It returns no semantic verdict. The command adapter is
`just measure-den-cnf ROOT [--eliminate]` (see the ir-text README).

Completion uses no extra head-disjunction variable, uses the head directly for a
single conjunction, reuses single-literal bodies,
and deduplicates bodies. Optional bounded CNF resolution eliminates single-reader,
single-definition acyclic atoms only, preserving input and recursive variables.
Each candidate allows at most 64 positive/negative clause pairs and must not grow
clauses or literal occurrences. The original ground graph is unchanged; removed
clauses retain a reverse-order model reconstruction log. Later query APIs must
protect or translate any eliminated query targets. This is a size experiment,
not a SAT checking backend or an execution planner.

Input at-most-one clauses use the same encoding here and in the SAT engine:
pairwise exclusions through five candidates, then a one-way sequential prefix
counter. Five candidates need ten clauses either way, so pairwise avoids three
registers at no clause cost. Larger groups need n-2 private auxiliaries and 3n-5
binary clauses. Exactly-one adds the positive coverage clause. Prefix registers
are existential auxiliaries, not equivalent named conditions; selector gating
applies to every clause when used in a query.

`Measurement::simplify_comparison` (CLI `--simplify`) independently measures
structural sharing, constants under U, dead bodies/redundant premises, syntactic
subsumption, and their composition, with baseline/elimination controls. Only
acyclic derived heads are rewritten in this increment. Inputs and recursive
boundaries are distinct terminals. Local BDD proofs expand bounded provider cones;
complete cardinality groups are included when they fit, otherwise that restriction
is omitted conservatively. No global conditions or selected assumptions are used.

Every variant starts from the original graph. Sequential rewrite records identify
aliases, constants, removed bodies and implied premises against the transformed
snapshot. The alias table restores original atom identities. These records and the
original rules remain available through encoding; the comparison API returns size
summaries, not a checking or witness API. Local proof exhaustion leaves the candidate
unchanged. Global budget exhaustion, cancellation and deadlines abort the report.
The report separates model, mapping, rewrite-record and CNF reconstruction vector
storage; the mapping is included in the model total. These exclude allocator and
map/set scratch overhead, BDD workspace and the retained original graph.

The measurement report also describes original residual recursive components,
before simplification: positive/negative SCCs, exact size histograms, counts above
100 atoms, rule-instance counts and relation membership. A negative component has
an internal negative edge; a positive component downstream of one stays positive
in this report.

`Measurement::first_local_difference` compares two local allowances on the same
original acyclic snapshot and returns the first proof lost under the second one.
It records expanded definitions, free cut points, included/omitted input groups,
work, cumulative created BDD nodes and the cutoff. This separates a local resource
effect from sequential composition; it does not explain every difference between
two completed simplification runs.

## Experimental completion queries

Opt-in `Limits::completion_sizes` records preparation counts and each completion
solver's CNF variables, clauses, literals and encoding attempts, including cutoffs.
It is a per-invocation observation sink, excluded from cache identity. A separate
positive-support least-fixpoint pass uses the same finite domains and eligible
inputs as possibility grounding, ignoring negation. Its own work/atom/time allowance
copies the configured limits, with its cooperative deadline capped at five seconds
per grounding attempt even if the run's timeout is larger. Diagnostic time is
excluded from the preparation budget, including cleanup. Progress reports the
component, round and tuple count; a cutoff explicitly reports that checking
continues. Its exhaustion never changes a verdict. Disabled runs do not compute
that LFP. Rules and positive readers are indexed once. The pass is semi-naive:
seed producers run once, then only new tuples trigger their recursive readers.
Accumulated join indexes are extended, never rebuilt per round. All LFP tables start
concrete and empty (eligible inputs are seeded); joins use concrete tuples, never symbolic-full
tables. If a join would require unbound sort-domain enumeration, the optional
comparison stops with an explicit cutoff. Large concrete joins remain possible,
bounded by this pass's work, atom and time allowances.

For a completed GFP and LFP, `circularOnly` counts GFP minus LFP, with an optional example.
These atoms need circular support in the positive possibility abstraction; this is
not a claim that they satisfy the original completion equations. A downstream
acyclic relation can inherit such support. Partial descending rounds report observed
tuples, not lower bounds on the final GFP. An unfinished LFP reports a lower bound
and leaves `circularOnly` unknown. Components are positive **relation** SCCs.
The retained LFP membership sets add diagnostic memory/work; this is not a memory
optimization. GFP observation bookkeeping runs once per relation, including failed
joins, with no per-tuple clock calls. A complete descending relation table contains
the LFP, so its difference count uses the two cardinalities. Partial tables leave
that difference unknown unless the LFP is empty. Example lookup examines at most
1,024 tuples in deterministic table order; a positive difference can therefore
have no example. This bound never changes the count.
Measurements keep at most 128 preparation and 1,024 solver records per sink, with
omitted counts. Presentation shows the largest 32 relations/components and bounds
each component's relation list; full program counters remain available.

Completion CNF encoding runs a scope-local Fitting fixpoint before allocation:
facts and producer-less atoms seed propagation, inputs remain unknown, and only
certain bodies settle a head. Self-support remains unknown. W, H and assumptions
cannot justify folding. Original atom positions and equations remain available for
model validation and evidence. Normalized bodies are deduplicated, single literals
are reused, conjunctions are shared within a gate, and single-definition private
body registers are eliminated directly. All named atoms remain query/replay targets;
general named-variable elimination from the size experiment is not enabled.

W builds one input-universe encoding plus independent copies for restrictions that
actually have defining rules. Input-only restrictions use world variables directly.
Rejection uses the same classification equations for its two solves, switching H
and disabling candidate-exclusion clauses. Pair searches still need independent
interpretations, including a separate classification pair when eligibility is not
already known. This preserves free helpers and prevents downstream filtering.

Search size records include bounded per-encoding details: purpose, completion,
input atoms, true/false constant substitutions and newly allocated variables/clauses.
Constants include producer-less/out-of-scope slots; they are local to that encoding,
not program-wide semantic findings. At most 64 detail records are retained per
search, with an omitted count. Other clauses (gates, restriction formulas, differences,
exclusion cubes) contribute to the search total, so copy deltas need not sum to it.
Preparation also records the peak GFP atom-allowance demand, including a rejected
insertion. This is neither the sum across rounds nor peak live memory: an intermediate
possibility table can be much larger than the final ground program. The descent
limits are unchanged. The order now prioritizes concrete anchors as described below.
Work per preparation attempt includes provider scope discovery (and its shared index
on the first needed provider), domain validation, input setup, possibility descent,
instance construction and dependency graph analysis. Diagnostic LFP work/time is
excluded. Common verification setup and subsequent provider SAT queries are outside
those grounding totals. Partial records retain consumed work and the stopping error.

Planning also exposes `planning_outputs(path, targets, options)`: independently audit
classification and the input contract, then check existence on every accepted input
in the union of the targets' live cones and C(H), and ambiguity projected onto those
exact atoms. Declared decisions do not exempt an explicitly requested output from
uniqueness. Outside helpers and processing do not enlarge this scope. Without H,
all certified inputs are accepted and output meaning is still checked separately.
`prepare_for_planning(..., outputs)` prepares bounded input providers required by
explicit outputs without changing the verification's decision selection.

The planning foundation exposes `planning_context(path, options)` and
`planning_constant(path, target, scope, options)`. A runtime path pins actual input
atoms; derived pins are refused. Without a hypothesis, certified inputs are accepted
and output queries still check their own meaning. Context analysis reports accept, reject, mixed, invalid, inconclusive
or no permitted inputs, using the existing independent symbolic searches and the
second count without H. Selected assumptions are still audited over U.

Constant proofs range over accepted interpretations, either in C(H) or in its
union with the target's frozen live cone. Helpers remain free. An empty accepted
context grants no proof. A scoped constant proof is conditional on an interpretation
existing; it does not certify existence for every observation, justify fabricating
a raw input/task result, or decide acceptance. For `h() :- raw();`, raw is true
under H while an actual false raw input must reject. The planner must preserve
that distinction. The separate completion planner and `plan-den` consume these
queries for straight-line v5 plans with accept/reject control; the stable planner
remains separate. No general synthesis, session cache or performance claim is added
by these bounded operations.

`completion_query::Engine::prepare` prepares an authored completion verification.
It returns `Preparation::Ready`, `InputDomains` with provider failures, or
`Inconclusive` with phase/resource information. Invalid API requests and cancellation
remain errors. Completion validates its selected assumptions itself; the stable
validator must not be used to veto a completion result.

Preparation computes a greatest fixpoint of possibly true tuples, then joins
positive-premise tables before enumerating any remaining variables. Derived tables
start at the full finite domain, so unseeded positive recursion survives. Within a
positive relation SCC, evaluate relations whose producers are concretely anchored
before symbolic-domain fallback. Install each shrinking table immediately and
reschedule its positive readers; no anchored pending update is bypassed for a
symbolic expansion. A symbolic-full table becoming concrete with the same contents
only reclassifies pending work, without scheduling a redundant recheck. Anchoring
is monotone during descent and is cached within the preparation. For a concrete
shrink, joins start from removed tuples and collect affected heads; rechecking all
of those heads' producers preserves alternative supports. Delta joins use the old
tables at every other occurrence, including repeated occurrences of the changed
relation. This prevents missing a binding whose premises disappear together.
The zero-arity full domain has one tuple, so its first removal also has a delta.
Other symbolic-to-concrete shrinks still request a full recheck. Pending head sets
are bounded by the existing possibility tables; no second graph of producer
instances is retained. Index creation, delta joins and rechecks consume the existing
work/deadline allowance. Unanchored alternatives remain live. This computes the same GFP
by monotone chaotic iteration, for static providers and runtime grounding alike.
Concrete joins use hash indexes on bound columns and select the smallest current
bucket at each step; a large table with a selective binding precedes a small but
disconnected table. Bucket iteration remains deterministic. Negative premises,
unseeded cycles and domain fallback are unchanged.
Provider scope discovery uses one lazy dependency index rather than repeated full
corpus scans. Finite domains are validated and normalized once per completion
preparation. All provider attempts, provisional live-scope grounding and runtime
grounding borrow that validated value. Original advisory dependency templates and
their head index are built once and shared immutably by the temporary provider
engines and final runtime engine. None of this state survives into a new preparation;
domain, rule and eligibility edits rebuild it. A producer
is omitted only when some positive premise cannot be true in any completion.
Negative premises never prune possibility. This does not run stable least-model
folding, admission, input-pin discovery or reduct refinement. Retained instances
keep their original source occurrences; other legal derived tuples are false.

The grounder's live-instance graph fixes every verdict scope: classification,
properties, assumptions and static providers. Its positive-support greatest fixpoint
ignores negation and is independent of W, H and decision selection. Later solver
pruning must not change that graph. The original templates remain for circular-support
component identity and opt-in dead-producer explanations, not verdict reachability.

Assumption cones may be recursive. `assumption_analysis` checks each restriction's
whole formula, independently over U: two models differing in formula truth establish
ambiguity; a cube search finds inputs with no model. Helpers and even the restricted
relation's tuples may vary if the formula's truth does not. Each candidate W solver
uses separate equation copies for each assumption, sharing only inputs. Before
returning a candidate, an independent query rules out a false interpretation of each
recursive assumption. A false-model cube excludes only observations for which that
interpretation remains valid. Other assumptions, H and downstream equations cannot
influence this certification.

`AssumptionAnalysis` retains the assumption, a differing group and true/false model
pair, or a no-model input. Known failures are Errors. Checking proceeds on certified,
satisfied observations, retaining counterexamples. This increment marks every
universal result incomplete when any selected assumption is invalid or unknown;
an empty certified subset is not inconsistent W, all-rejected or a vacuous proof.

Static `within` providers require tuple-set determinacy, ignoring helper differences.
`InputDomainIssue` names input and provider, and carries an ambiguity pair, no-meaning
or resource exhaustion. A dependency test can use a provider's positive-support
upper bound to prove it unreachable; this provisional graph is never a query's
input universe. Dependent preparations stop on failure. Unused bounded inputs are
listed in `ignored_input_domains`; models return `None` for their tuples and expose
`omitted_input_relations`. World queries on those relations are refused. All live
processing rules, selected assumption/obligation/decision/hypothesis relations and
input-cardinality declarations count as dependencies. Selected notices currently
conservatively require all inputs. Input-independent positive recursion may have
multiple completion interpretations; stable least-model evaluation is not a fallback.

- `worlds(&WorldQuery)` searches W alone with optional input pins and excluded cubes.
  It returns a complete input observation, `NoWorld`, or `Inconclusive`. An empty
  query's `NoWorld` means the input contract is inconsistent; a pinned query's
  `NoWorld` means only that the query has no permitted observation. If the certified
  search is empty and global assumption validation is invalid or unknown, it instead
  returns `Inconclusive` (conservatively even for pins outside the bad input region).
- `observation(present_inputs)` treats omitted eligible inputs as absent. Outside W
  it returns `NotPermitted`. An invalid recursive restriction returns `UndeterminedAssumptions`. With H, it counts interpretations of H's live
  upstream ground cone satisfying H, projected onto selected decisions: one is
  `Accepted`, and several are `Ambiguous`. Zero triggers existence checking of the
  same cone without H: a model is `Rejected { without_hypothesis }`, no model is
  `ClassificationNoMeaning`, and exhaustion is `Inconclusive`. The second query
  stops after one independently validated model. An accepted result separately
  reports processing existence and decision determinacy: no meaning, unique,
  multiple or inconclusive. It retains the classification equations and H, pinning
  only established decisions, so helpers remain free. Without H it reports these whole-program
  interpretation outcomes directly, with no rejection classification.
- Models label their scope, retain the full input observation and return `None`
  for derived atoms outside that scope. They satisfy the original completion
  equations, checked independently of the SAT encoding. They are not finite
  derivations. `ClassificationWithoutHypothesis` models witness genuine rejection;
  they do not assert H. Uniqueness compares tuple sets of authored decision relations,
  ignoring helper and auxiliary SAT variables; omitted selection compares every
  original relation. `Unique` is uniqueness of that projection, not necessarily of
  all values in its representative model. If uniqueness exhausts,
  an already validated interpretation is retained without claiming acceptance.

`QueryLimits` bounds solves, solver polls, conflicts and propagations, in addition
to ordinary work/CNF/deadline limits. One observation query shares its allowance
across W, classification and processing; completed classification survives a
processing cutoff. Preparation is immutable and reusable; each query currently
owns a fresh SAT solver and no query cache. Program, domain, eligibility, assumption
hypothesis or decision-selection edits require new preparation. No result is shared with stable mode.

`Engine::check(keys, options)` produces a whole-verification report. It queries
W outside H symbolically, with separate classification sets (`exists`, `none`, `inconclusive`),
processing meaning and obligation results. Established witnesses survive cutoff.
Only confirmed unique decision classification admits a world to processing
obligations; unknown classification never completes a property proof.
`Classification::no_meaning` records worlds without an interpretation even before
H: invalid input, a diagnostic (decisions: "Classification no-meaning is a
diagnostic"). It is searched last on a bounded share; neither a finding nor a
cutoff fails the verification or makes it incomplete, and
`no_meaning_explanation` gives the odd loop active at the witness world.
`no_rejections` forbids genuine rejections only. An all-rejected context counts
classification no-meaning worlds as invalid and excludes ambiguity and unknowns. It is explicit, processing is not applicable, and processing
properties are vacuous; inconsistent W is a context error instead.

Property queries use the live obligation and classification cones and H.
A separate eligibility query confirms unique classification decisions for each
candidate observation, leaving helper assignments free. They search all relevant helper interpretations, so an
arbitrary classification witness cannot hide a property failure. An independent
failure remains visible when unrelated processing has no model.
Supported forms are empty and uniqueness, plus coverage/exactly-one on acyclic
input-independent cones. Other coverage work and notices remain unanalysed.
Returned property interpretations carry `ModelScope::Property`; presentation falls
back to the obligation instead of inventing finite-support attribution. Existing
obligation identities are reused. Only a bounded number of property examples is
retained; reducing that number cannot change required outcomes.

Ambiguity uses two equation copies sharing only inputs, with a difference in a
selected decision. Processing/property candidates cannot participate in the
classification eligibility query. Rejection searches for a classification model
without H, then proves that no model with H exists for that observation.
No-meaning searches choose observations independently of the target equations.
Successful existence checks exclude a generalized input cube: keep derived values,
retain one true producer for every true head and one false premise for every
producer of a false head. Inputs not needed by those witnesses may vary. This is
completion evidence, so circular support is allowed. Pair cubes preserve both
models. Exclusions affect candidate selection only; they never constrain W or a
subsequent certification query. Positive SCCs have a least fixpoint, so absence of
negative cycles proves existence without enumerating observations; it does not
prove decision determinacy.

Classification sets, processing existence/ambiguity and each property have separate
work/deadline budgets and incremental query solvers. `QueryLimits` bounds each such
search, in addition to individual observation queries. `max_worlds` now bounds
candidate observations per counterexample-guided search, not the number of concrete
worlds a successful cube covers. `max_tuples` still bounds property candidates;
exclusion clauses count against CNF/work limits. Difficult cubes can still exhaust
these limits and give explicit inconclusive results. No real-program throughput
claim is made.
`CheckOptions::meaning` currently accepts only `Full`.

`circular_support` is an optional advisory, off by default. After required checking,
accepted classification examples are sampled separately and tested for unfounded
support. Sampling and detection share the independent advisory allowance. The
checker reports actual supported positive cycles, identified by their original
positive component's semantic keys. It never adds stable loop clauses or rejects
those interpretations. `advisory_limits` is independent; example truncation and
exhaustion are reported separately and do not change required verdicts.

`dead_producers` separately requests a bounded advisory for dead instances whose
heads are in C(H) and whose premises would connect atoms outside it. One example
per authored producer names a positive premise outside the possibility fixpoint.
This may enumerate substitutions under `advisory_limits`; its truncation or exhaustion
cannot change required results. No removal edit is offered for a whole source rule
on the strength of one dead ground instance.

The SAT CLI consumes these reports and the shared completion presenter. A separate
completion planner uses the scoped planning APIs. Editor, scorecard and BDD checking
continue to refuse completion explicitly.

## Experimental stable queries

`stable_query::Engine::prepare` prepares one immutable corpus, resolved domains and
named verification. It shares fixed preparation and the existing assumption-cone
validation, then encodes the independently propagated residual rules, declared input cardinality
U and the selected restrictions. Propagation preserves the original stable-model
sets in every world and uses no input-group or selected-assumption reasoning. It does not invoke admission, compute global BDD W,
or use the measurement experiment's rewrites/elimination.

`worlds(&Query)` searches permitted inputs using the assumption definitions alone.
`models(&Query)` searches full-program stable models. Queries contain conjunctive
atom pins and query-local excluded cubes; world queries accept inputs only. Each
SAT candidate is checked against its reduct's least model. An unfounded candidate
adds an external-support loop clause, rejecting that interpretation without
excluding its input world. Program loop clauses remain behind the program selector
and cannot remove a permitted world that has no full-program model.

Answers are a confirmed model, `NoModel` (no stable model satisfies this query), or
`Inconclusive` with its resource/phase. Cancellation and invalid requests are errors.
Preparation can also fail or exhaust its limits. `NoModel` is not a uniqueness,
totality, consistency classification or obligation verdict. `Engine::check` provides
those classifications separately, as described below. The expression oracle is
described below; session/editor integration remains future work. Ordinary checking
still uses BDDs.

Models expose residual values plus lazily resolved fixed values; world answers
expose inputs only. Exact canonical query keys include the query mode, pins and
excluded cubes. A bounded FIFO cache and learnt clauses belong to this engine's
immutable verification only. A new program, domain or assumption selection requires
a new engine; nothing is reused through arena handles across preparations. Conclusive
cached answers are independent of later queries, and partial clause-emission failures
make the engine unusable until rebuilt. See the checker policies for allowances.

`check(&keys, &CheckOptions)` checks the prepared verification's `empty(R)`
and `at_most_one` obligations, all fixed obligations, and whole-program stable
meaning. Pass the semantic keys of the same corpus used for preparation. The report separates:

- Context: permitted, empty declared input universe, inconsistent assumptions, or
  inconclusive.
- Existence: every permitted world has a stable model, a confirmed no-meaning world,
  inconclusive, or deliberately not analysed.
- Uniqueness: at most one model per world, two reduct-validated interpretations of
  one world, inconclusive, or deliberately not analysed. This does not imply existence.
- Emptiness: distinct tuples present in at least one stable model, with exact counts
  or lower bounds and bounded examples. Each example retains its own world, full
  replay scope, dependency-cone inputs and separately bounded finite derivation.
- Selected obligation kinds and notices not analysed by this increment.

Only the complete report's `proved()` combines context, existence, uniqueness and
all selected obligation results. In particular, zero violating stable models does
not hide a no-meaning or multiple-meaning world. Notices remain advisory.

`CheckOptions::meaning` selects `MeaningMode::Full` (default), `Uniqueness` or
`None`. Skipped phases return `NotAnalysed`, not an exhaustion or proof, even for
stratified programs. Properties and fixed results keep their own scopes and verdicts.
An explicit skip makes the aggregate report incomplete; switching modes on the same
immutable engine cannot reuse a whole-check result because those reports are not cached.

`Engine::prepare_scoped(..., PreparationScope::ObligationCones)` isolates the union
of the selected obligations' original grounded dependency cones. Use
`CheckOptions { meaning: MeaningMode::Cone, ..Default::default() }` for existence
plus universal property checks, without requiring uniqueness. `proved()` then
requires existence and all selected obligations, and the report names its scope.
Asking for cone mode on a whole-program engine is an invalid request: scope is
immutable and must be chosen at preparation. `Full` on a scoped engine also checks
uniqueness **within that scope**; the CLI only exposes existence-only cone checking.
`PreparationScope::Roots(Vec<GroundAtom>)` provides the same mechanism for explicit
outputs. The execution planner uses this scope with `Full`: both existence and
uniqueness are required within the output cone, and all planning oracle queries
use the same engine. Outside rules are explicitly unanalysed.
`RootsWithDependencies` adds caller-supplied upstream edges to that original cone
closure, for dependencies such as opaque producer arguments that are not relational
rules. Edges only select scope; they add no equations or assumptions. The closure is
transitive, budgeted and prepared before SAT encoding. Unreachable edge sources do
not enlarge the cone.

The cone follows original ground dependencies, including fixed evidence, before
independent propagation and producer removal. W is encoded from the unrestricted
program first; cone completion drops out-of-scope rules and does not reimpose
assumption restrictions on omitted derived atoms. Both obligation queries and
meaning fallbacks use the resulting isolated program, never whole-program equations.
A cone model need not extend to the whole program. Models return `None` for derived
atoms outside scope, and queries/oracles reject them. All inputs remain available.
Scope-specific clauses and cached answers belong to their own engine. Legal absent
tuples of selected relations remain in scope and read false; they add no ground
dependencies or inventory entries.

This increment still grounds the full program and retains the original atom slots
and evidence graph; cone mode limits semantic search, not preparation memory.
Scope construction is charged and may exhaust. Cone examples use `ConeOnly` replay
scope and original derivations. Advisory producer notices are included only when
all their represented instances lie inside the cone. An empty selection has an
empty cone but still requires a consistent W.

SAT preparation now also proves verification-local input pins on the independent W
encoding. It first confirms a permitted world, then tests the opposite of each
candidate input's observed value. Only UNSAT establishes a pin; unknown queries
leave inputs unfixed, and inconsistent W establishes none. The shared ground-atom
propagator folds the executable view under proved pins **before** program completion
is encoded. Assumption validation, W construction and ordinary BDD checking retain
their unrestricted graphs. `prepared_value` and the plan driver see values valid
under this verification's W; original rules still supply diagnostic derivations.
Only independently justified producer notices are published.

`QueryLimits::max_pin_candidates` (256, zero disables) and `max_pin_work`
(inheriting checker `max_work` by default) bound optional discovery. Inputs reaching negative components come first, with
semantic-key ties; unnamed inputs are skipped for bare query clients. Unknown or
truncated discovery is reported by `pin_stats()`. Proven literals are available via
`input_pins()`. A `SatInputPins` receipt records optional query work; preparation
records the subsequent propagation/encoding. Clauses from a failed partial query
append are discarded before the engine is published.

`CheckOptions::splits` enables a single level of exactly-one **input** partitioning
when negative components remain. Candidates are declared input cardinality groups
or selected exactly-one assumptions directly over inputs. At-most-one, coverage-only
and derived groups are ineligible. Ranking uses only the shared propagator over
negative components' upstream rules. It minimizes the descending vector of remaining
negative atom counts (worst branch first), with semantic group order breaking ties.
`SplitOptions` bounds candidates (8), members (32) and ranking work (inheriting
checker `max_work` by default); zero candidates disables splitting. `relation` optionally restricts the choice.

Each selected member is pinned true and its siblings false. W-only queries discard
empty arms. Nonempty arms own isolated solvers and pinned views; stratification proves
meaning immediately, otherwise the existing component search runs within that arm.
There is no nested split and no extra pin-discovery search within an arm. Existence
and uniqueness are combined independently across the covering partition. A confirmed
failure survives an inconclusive sibling; proof requires every nonempty arm. A
ranking cutoff keeps only completed rankings, or falls back to unsplit meaning.
`Meaning::split` reports the chosen group and each arm's phase results/stratification.
Properties continue to query the parent engine, and no arm's pins, clauses or caches
escape to it. This checker-owned meaning partition is also used by planning's
meaning prerequisite; it does not construct execution-plan branches.

Ground stratification after independent propagation proves the requested meaning phases without search. For
unstratified programs, existence independently chooses permitted worlds. Its cubes
preserve one finite positive derivation per true atom and one false premise per
producer of a false atom, rather than every alternative producer's truth. Only the
checked cone's inputs can enter its certificate; U/W remain separate.

Negative components are searched in dependency order, with their own compact upstream
cone encoding, reduct validation and exclusions. A reader requires upstream existence
and uniqueness proved for that cone itself. Positive components preserve this property
only when upstream is determined. Ambiguous upstream triggers a full-program fallback;
local ambiguity is not a global finding. Eligibility, certificates, component searches
and fallback share one existence allowance and the ordinary per-query limits. Each search owns a selector and appends each
cube once; its mutable queries bypass ordinary answer caching. Ordinary world,
program and property queries keep their separate selectors and immutable cache keys.
Partial append failure still requires rebuilding the engine. Final `ExistenceStats`
and throttled progress expose cube widths, distinct inputs, whole-program encoded
input support and exclusion/selector emission; `scopes` adds per-cone counters,
processing position and result/eligibility state, with `components_total` and an optional
fallback reason. Component ordinals identify this prepared graph only. Measurements
do not change cube selection.

Global uniqueness reuses completed negative-cone proofs from this check. If all are
existent and unique, no global pair query is needed. Otherwise it queries the downstream
closure of uncertified negative components plus upstream dependencies, excluding
unrelated positive work. Unclassified components stay in scope, including when existence
is skipped or incomplete. A scoped pair must extend through two full-program,
reduct-validated queries before it becomes a counterexample. An absent or inconclusive
extension triggers the whole-program pair query with the remaining phase allowance.
`UniquenessStats` reports scope, downstream component ordinals, encoded atoms/inputs,
query attempts and fallback reason. Proofs are invocation-local, not extracted from
those measurements. Selectors and loop clauses cannot constrain later world queries. No original rules are rewritten or admitted by these checks.

`denotate-presentation::emptiness_finding` shares the ordinary emptiness wording,
identity and derivation placement. A SAT example's negative premises are absences
in its validated stable interpretation; they do not assert that the interpretation
is unique. Callers must retain the separate meaning report. Editor publication
and session reuse of these reports remain future work. The CLI exposes these reports
with `--engine sat`; it uses the same property findings and placement as ordinary
checking.


### SAT CLI property checks

The experimental API also checks `at_most_one` with a selector-gated, linear prefix
encoding of "at least two tuples in this group". Each answer must pass the original
reduct validation; query exclusions cannot remove worlds from later questions.
Counts refer to distinct tuples, not their producing rules. Findings retain a world,
original derivations and the conflicting tuples' input dependency cone.

A relation with no residual ground atoms is fixed: every possible tuple has already
been settled by fixed preparation, and all other tuples are absent. All obligation
kinds on such relations are checked directly, including coverage over the resolved
grouping domains. These results use a permitted input observation and cone-only fixed
evidence; they survive unrelated no-meaning components. They are not claims that a
full-program stable interpretation exists. Symbolic coverage/exactly-one and notices
remain explicitly not analysed. The overall report still requires whole-program
unique meaning for a proof.

Uniqueness source attribution can exhaust independently of checking. Its
`Counterexample::incomplete_attribution` records missing tuple derivations, while
confirmed tuples remain failures. Ordinary BDD constructors leave this map empty.


### Stable expression oracle

The same immutable `stable_query::Engine` provides four driver-facing operations:

- `feasible(&context)` returns a stable interpretation, `NoModel` or inconclusive.
  This is full-program feasibility. Use `worlds` to ask about permitted inputs
  independently of whether the program has a meaning there.
- `constant(&context, &target, &allowance)` proves a Boolean constant or returns
  stable interpretations of both values. An infeasible context is a separate answer.
- `equivalent(&context, &target, &available, &expression, &allowance)` checks a
  supplied expression by asking SAT for a mismatch. A counterexample passes the
  original reduct validation; an infeasible context is never a vacuous success.
- `synthesize(&context, &target, &available, &allowance)` first checks for constants,
  then splits on available values in caller-supplied order. It returns an expression,
  two interpretations agreeing on all available values but differing on the target,
  infeasibility, or inconclusive. Exhaustion is not evidence of non-expressibility.

`Query` pins and exclusions describe the complete path context. Available values
are **not** pinned true: the execution driver promises that their runtime Boolean
values are known. They may be derived atoms. The oracle can reason through any
program definition, but the returned expression references only the supplied values.
It does not decide their readiness or schedule computations. A proof is relative to
stable interpretations of the context; it does not establish existence or uniqueness
in every permitted world. Keep the meaning checks separate.

`Expression` is a topologically ordered Boolean DAG of constants, atoms, not,
and, or and conditional nodes. Child indices precede parents. Supplied DAGs and
available atoms are validated even in infeasible contexts. `dependencies()` reports
reachable leaves; `evaluate()` uses only caller-provided Boolean values, without
consulting a checker model. Synthesized expressions share identical nodes, omit
identical branches and remove unreachable nodes. Branches with no stable models are
don't-cares. This is a deterministic reduced decision DAG for the supplied order,
not a claim of a minimal expression or equivalence outside its context.

For example, `x() :- a(), !b();` with both input atoms available synthesizes the
function `a && !b`; neither available atom is assumed true. With only `a` available,
the oracle returns two interpretations with the same `a` but different `x`. For
`p() :- flag(), !p();`, the context `flag = true` is infeasible for full-program
models even though it is a permitted input world. A caller must not mistake that
answer for input impossibility.

`OracleLimits` bounds compound queries, split branches, expression nodes and available
values. One work/deadline allowance covers the entire operation; primitive solves
retain the existing SAT limits. Exact context queries reuse the engine's bounded
cache. Supplied-expression mismatch encodings are selector-isolated and currently
rebuilt on each call; no separate expression cache or unsat-core generalization is
introduced. All state belongs to one prepared verification. The experimental
[plan driver](../plan/README.md) now consumes these operations, with `just plan-den`
for export. There is no editor or session integration for them yet. `Engine::meaning`
exposes the existing whole-program meaning checks independently of obligation
checking; callers establish context consistency separately. `program()` and
`prepared_value()` expose the immutable original graph and input-independent truth,
without admission or new semantic evaluation.


### Settled atoms in input-dependent relations

The SAT engine and assumption/W preparation share ground-atom propagation. It can
settle one tuple even when other tuples of the same relation depend on inputs.
A worklist follows satisfied or violated premises; negative cycles without an
independent proof stay unresolved. This is not SAT sweeping or admission.
The original graph is retained for findings and finite reduct derivations. The
view keeps all atom indices, including false atoms, and represents true heads by
one unconditional producer. `Engine::prepared_value` exposes the proved values;
`original_program` and `original_instance` expose original evidence. Query models
retain original atoms, so folded true outputs never become absence.

`Engine::preparation_receipts` includes the independently bounded settlement pass.
The specialization is tied to the full immutable program, domains and limits;
it is rebuilt on input-dependent edits even if the older relation-level fixed
fold is reused. Ordinary BDD admission retains its original graph and warnings.
Previously invalid assumption cones can now become valid through propagation.

SAT reports also carry advisory `subsumed_producers`, grouped per source rule.
A producer is reported when its head has an independently settled true
producer whose supporting proof uses no instance of that source rule, or when a
surviving producer's signed body is a subset of its body after propagation.
Syntactic subsumption also applies to recursive heads: it preserves each reduct's
least model. Equal bodies keep a survivor in semantic source/grounding key order.
Bare query callers may supply partial keys: heads lacking the necessary ordering
keys keep their producers, preserving the existing keyless query API.
The shared view drops subsumed rules before component analysis; original instances
remain available for evidence. Partial coverage lists the affected instances.
No removal edit is offered. Advisory work
has its own allowance, and `subsumption_incomplete` reports truncation without
changing any verdict. Default BDD/editor publication is deferred.

`Engine::negative_components` reports the specialized graph without any SAT query,
including when meaning is disabled. Components and relation counts use semantic
key order. Each sample cycle starts at a deterministic negative edge and follows
a shortest return path; at most twelve edges are retained. Reporting has a separate
caller-supplied allowance and marks incomplete output without changing verdicts.
View-local cycle rules map back through `original_instance`.


Completion size reporting does not itself run the diagnostic least fixpoint. Use
`CompletionSizes::with_least_analysis()` to request that independent bounded pass;
`CompletionSizes::default()` records preparation, joins, SCCs and search sizes only.
`preparationWork` includes stage times and work per authored join rule/stage; phase
counters use interned slots on the hot path. `Limits::run_deadline` optionally bounds
multiple operations cooperatively and is carried by `OperationalLimits`, never by
semantic/cache identity. Default Rust limits leave it unset. The SAT CLI policy is
separate; see [checker policies](../../docs/checker-policies.md#sat-cli-exploration-policy-2026-11-22).

Completion existence checks totality per negative SCC over unconstrained provider
atoms. Positive SCCs always extend their providers. A failed local check retains
that component and its upstream cone for the global W search; it cannot itself
produce a no-meaning finding. Processing keeps C and H in that fallback. The
existence encodings and cubes keep the reduced view's cyclic SCCs, H, restriction
targets and their upstream closure. The remaining acyclic equations are recomputed
in topological order before original-equation validation; they may vary with inputs
outside the cube. Lifting still requires a SAT proof that the retained equations
hold after removing a pin. This preserves the frozen semantic scope. Ambiguity pair
queries use the same projection with the compared decision atoms as extra roots and
replay reported pairs in full; property encodings do not use it. See the
[presence repro](../../fixtures/completion-lifting-scope/README.md).

`CompletionSearchSize::existence` and `CheckingTarget::CompletionExistence` expose
rounds, cube pins, validation work, total/fallback component counts and lifting.
These are observations, not certificates or stable identities. When a run deadline
is configured, completion divides remaining time among remaining required queries;
a query's local timeout does not restart the run deadline or suppress later work.

Completion processing/property searches establish eligibility before validating a
candidate's whole model; on success they restore a candidate on the same input
observation. Eligibility cubes now use block lifting for each model, with H kept
and the two cubes intersected. Their validation and property-model validation are
incremental against original rules, scoped to one immutable encoding.

Property parts reuse one W/cone solver. Conditions are temporary assumptions;
classification exclusions alone are shared. A prior validated model can witness
another `empty` tuple. Each part retains its SAT allowances, while work, physical
CNF retention and deadlines remain bounded across the whole obligation. Model
caches and reader indexes are invocation-local and never survive preparation edits.

Completion existence now tries call-consistency first: signed SCCs without an odd
negation cycle are total for every boundary assignment. Remaining search is confined
to odd-cycle cores and their providers. Input-relative signed graph certificates
may generalize a cube without fixing derived values; they complement, rather than
replace, the existing model certificates. Local non-totality still requires the
upstream W/context query before reporting a no-meaning observation.

`CompletionSearchSize.work_by_phase` separates cumulative query costs from the
operation at which an allowance ran out. `CompletionExistenceStats` retains bounded
component details and a current component during search, including parity conflicts.
`CheckOptions.max_failures` bounds completion failure triage separately from retained
examples. `ObligationResult.failures_truncated` makes counts lower bounds; a confirmed
failure can be complete as a verdict without enumerating all failed parts.

Component records label the reported graph's scope, W/W+H context and pruned/unpruned
view, including H-first classification's W-pruned shape records when pruning is enabled.
Odd component details include bounded structural explanations when progress or
size recording is enabled: signed cycles, exact source rules, alternative
producers and their other conjuncts, negative-edge relation histograms, and
guard-input groups. The checker retains RuleId provenance through compact
component views; text adapters resolve locations from immutable source snapshots.
Parity-doubled BFS finds a shortest odd return walk for each selected conflicting
edge, then removes closed subwalks to retain a simple odd cycle. This is not a
global shortest-cycle claim. An odd cycle explains why call-consistency failed;
it does not prove that the equations have no model. Guard inputs are structural
reachability candidates, not validated split or pruning recommendations.

Verification-wide completion ambiguity uses componentwise determinacy. Acyclic
functions of shared providers and locally unique cyclic components share literals across models. Local
uniqueness is an independent two-copy SAT test with free boundary atoms, not a parity
test. Non-unique local components are checked for reachable decision differences
under W/H; coupled choices retain a joint residual fallback. Shared gates preserve
original equations, and both returned models are replayed against them. The query
retains existing limits and reports local/reachable/coupled component sizes and
states before each solve. A local `fallback` is not a semantic ambiguity result.

Completion whole-verification checking with `CheckOptions { prune: true,
..Default::default() }` simplifies solver views with **common-equations proofs**: coverage makes a head true, and subsumption removes a producer implied by
the remaining producers. The head's own definition is disabled while proving the
replacement. The current other equations stay present. Proofs are local to the
original classification, processing or property scope, and to W or W+H; no simplified
graph defines a scope. W/provider/assumption construction and the stable checker
are unaffected. Models are still validated against the original scoped equations.

`completion_query::Report::pruning` contains bounded `PruningRecord`s (head, source
instances, scope and context), aggregate attempts/removals/coverage, omitted counts
and optional optimization cutoffs. `views` reports scope/context, round count and
`saturated`, `candidate-cutoff` or `overall-cutoff`. Changed rounds rediscover targets
and retry earlier failed candidates. Saturation requires a complete unchanged round
without unresolved attempts. A cutoff does not itself make checking incomplete.
Views live for one `Engine::check` call; repeated/fresh calls recompute them. The
unpruned implementation and exhaustive interpretation tests remain independent
semantic controls. H-model coverage now precedes no-H classification existence
queries; only confirmed absence of an H-model permits the latter query.

`CheckOptions::prune` defaults to false. The CLI exposes it as
`--completion-prune` with `--engine sat`. Disabled checks use the original query
path without the pruning cache or H-first existence search. All completion views
receive the search-free reductions described below, and original-equation
validation applies in both modes. `Report::pruning.enabled` identifies opt-in reports; the shared
presenter omits `simplifications` entirely when disabled.

Optional pruning targets only odd or independently locally non-unique cyclic
components, using parity witness cycles and negative-edge relation histograms.
Multi-producer heads get round-robin turns before unary heads; each proof retains
the common-equations contract above. A bounded invocation/view/candidate time share
prevents this optional work from taking the entire checking deadline (see checker
policies). `PruningReport.components` reports candidate, considered, proved and
removed counts, ranked example heads, last attempted head, elapsed time and cutoff.
H views extend the W-pruned view; classification's structural check and no-H fallback
also use it. There is no H-dependent proof in a W view.

After reachable determinacy pairs prove no difference, a cheap conservative check
can skip the coupled query when all original downstream closures are disjoint.
Shared hidden constraints retain the coupled fallback. `coupled_fallback_skipped`
records this shortcut; large scopes decline it without changing the query path.

### Opt-in completion input partitions

`CheckOptions::split_depth` (default 0) enables branch search for verification-wide
existence and determinacy. `split_branches` (default 512) bounds the leaf partition
per question. The CLI exposes `--completion-split-depth N` and
`--completion-split-branches N` with `--engine sat`. Zero depth takes the existing
unsplit path. These options do not change obligations, planning queries or W
construction.

Partitions use declared or selected input at-most-one/exactly-one groups. A
selected derived assumption also qualifies when its own equations, after Fitting
under the branch pins, map every unfixed member to exactly one distinct positive
input literal. There must be one live producer and all other conjuncts must be
true; fixed-false members contribute nothing. H and processing conclusions cannot
justify this certificate. Without a useful certified group, split one input into
true/false cases.

Follow guard providers only through acyclic atoms. Rank a bounded shortlist by
structural edge influence within each kind, alternating inputs and formulas in
the inventory and eight trial slots. Unused slots pass to the other kind. Trial
allowances are shared, including failed candidates. Prefer total per-child witness
cuts per extra child, then common cuts and actual disabled edges per extra child; parallel producers keep their edge alive. Trials have a bounded share of
setup time/work, and incomplete trials leave residual search available. Telemetry
records up to 64 candidates with context, state, checked children, disabled-edge
counts and omitted candidates, plus the next verified alternative. Only
distinguished values receive their own child; one
rest child pins those values false and leaves other values unknown. At-most-one
rest includes absence and can be split again later. Exactly-one rest remains
subject to W's coverage requirement. A value child excludes siblings by the
certified cardinality, not by Fitting.
Each child applies Fitting propagation before parity/local uniqueness and residual
search. Scopes stay frozen. Reaching depth or leaf bounds uses residual search;
resource exhaustion remains inconclusive. A confirmed failure in one child survives
another child's cutoff; absence of a failure requires every child to finish.

Ordinary processing-existence and ambiguity questions rank before searching.
Without a verified witness cut in any child,
it runs unsplit once with the remaining allowance, including on an inconclusive
result. Otherwise one unsplit attempt gets half the remaining allocation; only an
inconclusive result uses the reserved half for the already ranked partition.
Classification existence instead runs the structural driver before its cover.
Exploration uses the probe-first policy described below.
Traversal is breadth-first, with an absolute per-unit cutoff shared by its nested
queries and bounded by the outer question deadline. Untouched components remain
rankable in every path. If a selected target is cut on only one side, explore that
side and residual-check the unchanged side of that target; other components on
both sides can still compete. A later split rediscovers components under its new
pins. No closed witness implies that other components are solved. Child ranking
leaves time for residual checking when no useful partition is found.

Pruning views are built before these allocations. One aggregate pruning allowance
is reserved fairly across verifications, scopes and W/H. Saturated classification
and processing views release unused time equally to unstarted buckets within the
verification; cutoffs and unfinished views do not. Property cones keep their shared
reservation. Processing prioritizes classification-W successful heads, re-proving
their rewrites in its own scope. H-only proofs and capped presentation records are
not the source of these hints. Per-view telemetry reports allocation, elapsed and
released time, and prioritized attempts/proofs. CLI automatic time-scaled
search guards survive branch division, including preparation cost; explicit caps
still divide, structural caps stay separate, and every child shares the absolute
run deadline. Library defaults remain unchanged. See checker policies for amounts.

Units share copy-on-write rule/atom tables and read-only incidence indexes.
Children inherit paged Fitting state and propagate only newly pinned inputs;
unchanged pages stay shared. Materializing fixed values for a query still scans
the value array, but does not copy program rules. Units own solver state,
work/query allowances and size records. Explicit work and query allowances are
divided among children; the phase deadline is shared fairly among pending units.
`Report::branches` reports bounded choices, outcomes, work, time and cutoffs.
Repeated/fresh calls rebuild units. Cross-call caching and parallel execution are
not implemented. When pruning is enabled, pinned units inherit the ancestor's
W view for no-H queries and its stronger W+H view for H-context queries. These
context-tagged caches also accept branch-local common-equations proofs when both
pruning and splits are enabled. Bounded discovery includes alternative-producer
guards of witness heads. Trial views retain complete canonical assignments and are
handed to selected children; siblings and weaker contexts cannot reuse them.
Proof setup uses explicit assignments and ancestor proofs, not ordinary Fitting
conclusions. Failed/discarded attempts consume the shared trial ledger, including
setup and local uniqueness queries. W and H have independent reservations funded
by ranking; root shares and redistribution priority are unchanged. Only genuinely
leftover released root time can supplement ranking, transferred once inside the
question deadline.
Conditional source records are published only for selected partitions; all trial
attempts/proofs/time remain telemetry. Original scopes and residual queries remain
unchanged. Derived guards with wholly acyclic upstream are also two-child formula
candidates. `SettledAtom` certificates retain original scope, W/W+H and a compact
input formula; `Pin` carries its branch value. Fitting substitutes the atom only
in matching views, while each residual solver also asserts and independently
replays the input formula. This prevents substitution from dropping the atom's
meaning and admitting spurious inputs. Assumption/universe equations remain intact.
H-only certificates cannot split no-H work: mixed classification-existence questions
use W-valid formulas only. No forcing is implemented.

Selected candidates share a 32-guard diagnostic cap across every child; unused
shares pass forward. Child records include omissions/completeness, pruning
removals, bounded pruned heads, settled target atoms and witness cuts. A closed
target still receives the full residual question.

Completion proof-based pruning also shortens bodies in targeted odd/non-unique components.
A positive literal L is removable from `x :- A, L` when the other equations and
recorded context imply `A -> L`. A one-atom producer for L whose atom is in A
provides an indexed structural proof (L must differ from x). Otherwise the shared
SAT proof disables x's equation, tests the implication, and updates its gated
replacement. All later proofs use current equations. The SAT proof path is opt-in
under the existing pruning option; the structural path runs on all rules before
analysis. No source scopes, input contracts or validation rules change. Literal removals have separate counts and evidence from producer removals,
and shortened instances retain their original ground-rule source identity.


### Search-free completion views

Before structural analysis, each classification, processing and property solver
view propagates facts using Fitting's three-valued fixpoint. Fixed heads have no
active producers; a false body has no active edges; known-true body literals can
be dropped. An indexed worklist then removes positive body literals implied by
another conjunct through a unary positive producer, across all live rules rather
than only optional pruning targets. Newly unary producers wake their readers.
This requires neither H nor a SAT proof, and also runs with pruning disabled.

Components, odd witnesses, existence shortcuts and branch ranking use the reduced
view. Branches inherit the reductions allowed by their W/W+H context and pins;
materializing an analysis view does not change incremental child propagation.
Original source rule slots remain for identity and replay. Frozen live-GFP scopes
(C(H), properties and contracts) do not shrink. Returned models are checked against
the original scoped equations. Positive self-support is not forced false: this is
completion-preserving Fitting, not least-model or well-founded evaluation.

Reduction work uses the caller's existing budget. Initial reduction precedes the
optional root SAT-pruning pass; reductions between proof rounds also remain subject
to that pass's elapsed-time bound. A cutoff keeps the supplied equations, with spent work still charged;
cancellation propagates. Optional pruning retains structural removal evidence;
pruning-off runs do not acquire new optimization findings. The public
[fact-guard pair](../../fixtures/completion-search-free/README.md) exercises an odd
cycle that exists only before these reductions.

### Opt-in completion forcing

`CheckOptions::force` / `check-den --engine sat --completion-split-depth 2 --completion-force` enables
path-local constant proofs for verification existence/determinacy searches. It
runs in funded split trials and residual branch units; it requires positive
split depth and is off by default. In ordinary mode, no extra root forcing pass
delays processing existence or ambiguity's established first attempt. Classification
existence uses the structural driver first. After Fitting
and applicable pruning, one fixed encoding per view answers both polarities of
remaining witness/loop atoms using SAT assumptions. Proven constants feed back
into propagation and pruning; newly acyclic dependents may become formula split
candidates. Trial ranking prefers witness atoms forced by the children, followed
by existing verified-cut ranking. No cut still means no partition.

The original defining equation of each forced atom remains a residual constraint.
For example, `x() :- i(), !x();` entails false for `x` wherever a model exists,
but still has no model when `i` is true. Encoding, replay, existence projection
and cube certification retain that constraint; having no remaining cyclic SCC
is insufficient to bypass it. H-context constants stay in H views. W construction,
obligations and planning are unchanged.

Forcing uses part of the existing optional ranking allocation and shares it
between applicable W/H contexts; residual searches retain their allocation.
Forcing answers SAT from an encoding-local model cache, re-solving every 100th
claimed hit as a tripwire (a contradiction is a hard internal error); core claims are
still only compared against the solver. `Limits::completion_cache_enforce = false`
keeps the cache in shadow mode, where every query is solved. Branch and trial-child
telemetry reports forced constants (32 named examples per pass), forced witness
atoms, candidate attempts, cache claims/checks/mismatches and cutoffs. A cache
claim interrupted before solving is not a checked hit. See checker policies for
storage and accounting limits.

### Completion exploration scheduling

`Limits::completion_exploration` / `just check-den ROOT --engine sat
--completion-explore` opts into exploration scheduling. It does not enable
pruning, forcing or splits: select those separately. BDD/editor defaults are unchanged.

Exploration removes implicit time/work/query subdivisions and the trial-start
floor. Questions run in this order: contracts/world, rejection, classification
ambiguity, accepted observations, processing existence, processing ambiguity,
obligations and optional advisories, then classification existence. Moving the
last question does not change its verdict or the aggregate status.

With splits enabled, the root and every child first try a bounded unsplit probe.
`Limits::completion_probe_work` / `--completion-probe-work N` sets its deterministic
work cap (256,000,000 by default; 0 disables it). Work includes SAT callback polls.
A conclusive probe skips pruning, forcing and ranking. The probe runs the ordinary
unsplit search, covers and lifting included, under that cap, reusing existing views
without starting pruning, forcing or ranking. An exhausted probe stays charged and
is never a proof. On probe cutoff:
reductions, requested pruning to saturation, requested forcing over all remaining
candidates, then ranking every shortlisted trial. Split on a verified cut;
residual search runs only at leaves (no useful split or a configured split bound).
Both cut and uncut children rank their surviving components. Traversal is breadth
first. Without splits the ordinary unsplit question remains the only search.

In ordinary mode classification existence keeps its bounded share of the remaining
question time, with component/cover progress and an explicit cutoff cause. When
splits are enabled, classification existence runs forcing and splits before cover
enumeration. Ordinary processing existence and ambiguity retain their established
first attempt before installing a forced branch view. Rejection and acceptance
keep their direct unsplit searches; their new branch driver is exploration-only.

Explicit resource limits, grounding/CNF/storage bounds, split depth/leaves and
cancellation still apply. A CLI invocation retains its shared timeout, 120 seconds
by default, across preparation and every selected verification. Use an explicit
larger `--timeout-ms` for a long exploration. Automatic search guards are fixed
at a generous value independent of that timeout; they are not calibrated performance
policies. API callers retain the limits they supplied. Without an API invocation
deadline, `Engine::check` establishes one shared deadline for that check.

The existing budget scopes remain: preparation and independent searches have their
own work limits, pruning views have their own proof allowances, and property parts
retain their existing query limits. Exploration siblings consume actual remaining
question work/SAT usage rather than receiving fractions or renewed allowances.
Trial ledgers retain spent work, including discarded children. This does not yet
replace solver limits with deterministic in-solve conflict/propagation interrupts.

Progress includes live work/solver-poll counters, trial and forcing completion or
cutoff, pruning stop reasons, and not-started/disabled stages. Counter snapshots are
local to the reported operation: nested scopes overlap and must not be summed.
Logging does not select candidates. The finite inventory/shortlist and bounded
witness/output caps are unchanged; completing exploration is not a completeness
claim about every possible rewrite or split.
