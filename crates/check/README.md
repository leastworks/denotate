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
A producer is reported only when its head has an independently settled true
producer whose supporting proof uses no instance of that source rule. Partial
coverage lists the affected instances. No removal edit is offered. Advisory work
has its own allowance, and `subsumption_incomplete` reports truncation without
changing any verdict. Default BDD/editor publication is deferred.
