# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Checker backend | BDD by default and in editors; experimental SAT CLI opt-in | Predictable, canonical conditions; good warm reuse |
| BDD input order | Semantic-key order; opt-in reverse and structural orders for diagnosis | Structural order helped only synthetic name-separated shapes; under 0.5% on a production-scale program |
| Relation-SCC grounding | Kept opt-in | Warm-run wins; not yet worth the complexity by default |
| Fixed-fact evaluation | Shared across verifications; one retained keyed fold per session, without a byte cap | Checker limits bound the fold; retain completed work for reuse across edits and report its accounted bytes |
| Admission rewrite order | Exact removals before bounds; component passes upstream first, each successful batch committed immediately | Preserve completed work before later components exhaust; rebuild ordering after every commit |
| Assumption validation | Ground-validate the union selected by executed verifications | Unselected cones need no grounding; selected cones still share whole-residual preparation |
| Plan cache | Small-rule bypass with bounded retention | Avoids caching cost for trivial rules |
| Coverage results | Recomputed each check; preparation is reused | No measured need for a coverage verdict cache yet |

Tried and removed: component-level evaluation, which lost everywhere it was measured.

Guarantees that are **not** provisional: cold and warm sessions produce identical
results and receipts; conclusive answers agree with independent small-world and
stable-model oracles; limits produce explicit inconclusive outcomes, never silent success.

To diagnose a slow or exhausted run, `just check-den ROOT` prints phases, prepared
sizes and the effective limits on stderr, and `--timeout-ms`/`--max-*` override
`Limits` for one invocation ([den-format](den-format.md#commands),
`just check-den --help`). VS Code exposes the same controls through
`denotate.timeoutMs` and `denotate.limits`, window-wide, with automatic rechecking.
These are explicit controls, not new defaults. Both frontends report the failure's
subphase, effective ceiling and observed demand where available. A stopped BDD
operation may not expose an exact count; no count is fabricated. Counts can include
rejected demand, and an effective ceiling can be tightened by remaining work/storage
or backend capacity. These diagnostics do not change accounting or semantic outcomes.

Completion's optional size diagnostics compare positive-support greatest and least
fixpoints without changing grounding. The least-fixpoint comparison has a separate
copy of the configured atom/work/time allowances; its time and cleanup are excluded
from the semantic preparation clock. Cancellation still applies. Diagnostic exhaustion
reports incomplete counts, never changes checking completeness or causes pruning.
The comparison retains additional temporary tables; enable it to diagnose size, not
to measure the uninstrumented memory/time baseline. No budget defaults change.

## IR construction

Constant duplicate validation uses an ordered name set per namespace/sort pair,
rather than scanning all earlier constants for every declaration. This replaces
quadratic construction work with logarithmic lookup in the relevant name set.
The index stores one additional owned name per constant and does not determine
declaration order, occurrence IDs or semantic keys. Error precedence and duplicate
rules are unchanged. This is construction bookkeeping, with no change to checker
budgets or deadline polling.

## Diagnostic input ordering

`just check-den ROOT --input-order key|reverse-key|structural` selects a BDD
variable order for that invocation. `key` is the unchanged default; the editor
and scorecards keep it. The schema and zoo runners accept the same option. This
is a diagnostic configuration, not a new limit or a new backend.

Ordering happens after fixed/`within` preparation and grounding, before W or any
input-dependent BDD. Structural ordering traverses the dependency graph, with no
symbolic evaluation: settled rule premises contribute input-support hyperedges,
as do selected assumptions. Input-only uniqueness groups receive extra weight.
Selected-assumption groups remain weighted preferences: they can overlap and their
members may be read with outside inputs. Declared at-most-one/exactly-one groups
instead form indivisible placement blocks. Their members are semantic-key ordered;
blocks tie-break by their minimum member key. Unconstrained inputs are singleton
blocks. Hyperedges attach to blocks, and eight FORCE passes use integer centers
and semantic-key ties, retaining the best weighted span cost seen. No
platform-dependent floating-point ordering is used. Assumption enforcement is
unchanged.

Declared groups partition the input atoms. Keeping each group's variables together
makes the BDD representation of U, and of each component's conjunction of declared
group masks, linear in the total group membership. This does not bound cumulative
construction work, total retained masks, arbitrary fact conditions or selected W.
Explicit `key` and `reverse-key` orders stay unchanged; a non-leading grouping
column can scatter their groups. The report counts those scattered groups.

The heuristic charges preparation work. Two configurable optimization allowances
bound it: `--max-input-order-entries` (default 1,000,000 peak retained placement
entries) and `--max-input-order-work` (default 4,000,000 cumulative work). Entries
count unique support members and container metadata, including temporary unions
and traversal stacks; they are not heap bytes. Canonical support sets and unions
of provider IDs are shared. A repeated edge still adds its weight without retaining
another support vector. Construction, comparison, sorting and traversal remain
charged work. Exact distinct supports can still have quadratic total size.

An ordering allowance cutoff returns `grouped-key` when nontrivial declared groups
exist: blocks in minimum-member key order, members in key order. Otherwise it
returns `key`. The report names the allowance, its limit and the observed demand.
Building the declared-block baseline is mandatory even when an optional allowance
is zero; its O(inputs) storage is bounded by existing grounding/input limits.
Its construction and fallback expansion charge global preparation work. The
heuristic additionally accounts the retained block arrays within its placement
allowance; block-baseline construction temporaries are outside that optional
meter. Spent work remains charged. Global work exhaustion, deadlines and
cancellation still propagate. Zero disables the corresponding optional placement
resource, not the mandatory block baseline. Key order remains the default.

The CLI emits requested/effective order immediately after selection, before W
construction, even when later preparation fails. Completed non-default runs also
retain the stdout summary. `inputOrder` includes requested/effective order,
fallback, `fallbackLimit`, `fallbackObserved`, inputs, `structuralEntries` (peak
retained heuristic entries), `structuralWork` (cumulative heuristic work),
`declaredBlocks` (nontrivial declared groups packed), `placementBlocks` (all
placement positions), `scatteredDeclaredGroups`, hyperedges and completed passes.
The early progress event carries no projected input atoms or source lookups.

The backend configuration includes the requested order (`structural-order-v4`
identifies declared blocks, including grouped fallback). The allowances
are part of deterministic request identity. Shared contexts partition
by selection and configuration; the assumption-specialized graph receives the
request's exact map before W is built. Local query inputs retain the actual ordered
input keys, including any completion context, so structural edits and switching
orders cannot reuse a result with the wrong map. Structural ordering currently
recomputes with preparation; choosing a default and an edit-stability policy are
separate work. Witness choices and rewrite-warning inventories may differ, since
guarded candidate priorities also use BDD sizes. Conclusive semantic answers must
agree; compare independent tiny-world oracles as well as completed workload runs.

Measured outcome: structural order cut BDD work sharply on shapes whose input names
separate co-read inputs (the zoo's guarded fan-in and ring), and changed little
elsewhere. On a production-scale lowered program (about 30K inputs) it completes
only with raised cutoffs (the support expansion is quadratic there) and moved BDD
node counts by at most 0.5% in every phase with the former hard-group placement.
That run preceded removal of the hard uniqueness blocks. A separate writer-ring
reproduction demonstrated that those blocks can dominate the cost by separating
each lane's route and flag inputs. Re-score the updated placement on the production
program before drawing a conclusion about its benefit there. Key order stays the
default and structural order remains a diagnostic. A default change would need
corpus-scale cutoff and support-expansion evidence, plus an edit-stability policy.
The weighted-span objective is not a BDD-size guarantee. Earlier unconstrained
preferences improved the writer ring while enlarging split-reader certificates.
With declared blocks, the 32-group interleaving control now completes where it
previously exhausted U construction. Conversely, the four-writer/eight-lane ring
changes from proved to deadline-limited under the same raised limits; the
four-writer/two-lane control still proves. Keep both trade-offs in placement
comparisons. Compact U alone does not guarantee affordable later conditions.

## Backend retirement

BDD remains the default and editor backend. The earlier SAT experiment showed wins on synthetic and
test-DSL workloads, but no demonstrated need on real programs. Maintaining it multiplied
implementation and validation work for each obligation kind and made diagnostics depend
on a setting. Its coverage path still depended on BDD evaluation, so it could not help
when that evaluation exhausted. Its backend implementation and selectors remain retired;
Git history retains the experiment. The diagnostic probe below and the new
experimental stable-query CLI separately use batsat; they do not restore that
retired implementation.

Revisit only for a real program that exhausts BDD evaluation within reasonable limits,
re-scored with the `.den` scorecard below. An alternative must demonstrate better
conclusive outcomes under comparable limits, while matching the independent semantic
oracles; inconclusive or unsupported answers are not wins. A second backend is not a
standing feature-parity requirement.

## Diagnostic SAT probe

`just check-den ROOT --sat-probe` asks whether an unresolved negative component
has two stable meanings in one permitted world, then checks for worlds with no
meaning when uniqueness is established. It is off by default. Queries run inside
admission, after structural reductions and producer removals reach a snapshot with
no further cheap removal batch, before bound removals and discharge attempts.
Components follow admission's provider-first order. Results go to stderr progress
and `--profile-memory` records; ordinary BDD verdicts, findings, stdout and exit
codes are unchanged. Neither an editor setting nor a second checking backend is
introduced.

The encoding contains the target component and the exact settled conditions it
reads, including existing replacement expressions, plus W (the selected
assumptions' already-computed permitted-world condition). Read-only Tseitin
encoding replaces upstream definitions. Anonymous acyclic Boolean definitions
participate in reduct replay and existence covers, so disabled guards cannot
silently become enabled inside a covering cube. Shared inputs and settled
conditions feed both completions; disagreement is required on the target only.
No additional BDD operations are performed. Domain overrides, `within` and all
assumption kinds are already reflected in these exact conditions.

An unsettled provider outside the target gives `unknown` with `upstream unresolved`.
After admission commits a rewrite, queries on the next snapshot can use newly
settled providers. Each reached snapshot is queried afresh: no SAT answer skips,
reorders or admits anything. Components removed by cheap passes need no query.
A limit before this diagnostic point can prevent a query; a reused admission or
inconsistent context has no admission attempts and emits no component probes.
The low-level `PreparedCheck::sat_probe` retains the earlier pre-admission
whole-cone query for explicit comparisons; the CLI uses the compact path.

Every candidate pair is independently evaluated as the least model of its reduct
over the whole encoded cone. Unfounded candidates add external-support clauses
valid for every stable model in every world. A verified pair is `sat`; `unsat`
proves **at most one** stable meaning per permitted world. It does not establish
existence, consistent assumptions or admissibility. Only UNSAT before any
refinement also excludes two supported models. Unrelated regions outside the cone
are not certified, so a verified pair is a component result, not a claim that the
entire program has two stable models.

Each component at each reached snapshot receives a fresh independent allowance. `--sat-probe-timeout-ms`
defaults to 10,000 ms per question (uniqueness, then existence after UNSAT),
including encoding, solving and replay; deadlines are cooperative. Existence has
its own fresh allowance and does not consume or reset the uniqueness allowance.
`--sat-probe-refinements` defaults to 64. Existing `max_atoms`, `max_rules`,
`max_dependencies` and `max_work` bound the cone and encoding: CNF variables,
emitted clauses and literal occurrences respectively share those size ceilings.
They do not consume the ordinary checker's allowance. Encoding, solving and
report delivery time are excluded from admission's deadline, preserving time
already spent on ordinary checking. The solver's learned clauses
are internal solver storage, not counted as emitted CNF; solving is time-bounded,
not a process-memory cap. Exhaustion gives `unknown` with a reason. Cancellation
propagates. No solver state or arena indices are retained between invocations.

Reports contain emitted CNF counts, solve time, refinement/solve counts and the
verified pair, with local source locations. These are observations, never goldens.
Use `just bench-den-schema --sat-probe` or `just bench-den-zoo --sat-probe` to retain
them alongside normal outcomes. After uniqueness is established, a separate
existence search reports `every-world`, `no-meaning` (with a permitted world),
`inconsistent-assumptions` (W is empty), or `unknown` with its reason. It uses the
same configured limits, freshly, and one aggregate refinement counter for both
world and model queries. World exploration also consumes work and emitted CNF
space, so incomplete search never means existence was established. There is no
additional world-count tuning limit. Reports distinguish proposed worlds and
emitted covering cubes; a cube can cover many concrete worlds.

The world query contains only W and its acyclic Boolean definitions; target
equations are disabled. The model query pins all cone inputs and enables the
target and exact settled-boundary equations. Both modes share one
SAT engine, so their combined emitted CNF size is bounded by a single allowance.
Loop refinements follow the appropriate mode; covering clauses apply only to world
proposals. A stable model supplies a sufficient cube preserving all true rule
bodies and one false premise of every false body. Derived premises keep the same
interpretation; only necessary input values are fixed. Thus support survives and
no previously false producer can become true. This is conservative, not a minimal
cube, and is not the unsound shortcut of retaining only successful derivation
leaves. An input-independent model can cover the entire input space.

Only `unsat` plus `every-world` establishes exactly one stable meaning in the
probed cone; it still does not admit the program or establish anything about
unrelated regions. Unresolved upstream components remain unknown in this increment.
Admitting programs based on SAT stays a separate future choice.

### Committed program exports

Committed-program export (`--export-committed FILE`) is a separate experiment for
skipping already-committed proof search on a later run. It does not retain BDDs;
loading, grounding, preparation and symbolic evaluation recur. Measure these phases
separately. Independent defaults are 100 million traversal work units, 1 GiB of
output and 120 seconds (`--export-max-work`, `--export-max-bytes`,
`--export-timeout-ms`). These bound streaming output and temporary expression/name
indexes; they are not an exact heap-byte budget. Export time is excluded from
admission's deadline. Failure cannot change a verdict or publish a partial file.
An explicit `--stop-after-round N` instead intentionally skips checking and returns
incomplete (2), without caching partial admission. See the
[export guide](../crates/ir-text/README.md#committed-program-experiments).

### Component dumps

`--dump-component FILE` records actual guarded attempts and the final committed
unresolved graph under an independent diagnostic allowance. Default file-wide
limits are 100,000 data records, 2 million traversal work units, 32 MiB each of
serialized data and copied name text, and 10 seconds of active recording time.
Half is reserved for attempts, half for final graphs/contexts. Collection and
expression-depth caps bound temporary formatting; these are not exact heap-byte
limits. Small control records survive data truncation. Recording time is excluded
from admission's deadline, and a diagnostic failure cannot change its result.
Details and limitations are in the [dump guide](../crates/ir-text/examples/check/COMPONENT-DUMP.md).

### Guarded-candidate filter

`--sat-probe-candidates` separately opts into a necessary-condition query at the
actual guarded-settlement snapshot, after earlier rewrites and implied-guard
strengthening. It runs when admission selects a candidate for bounds iteration, after the
final implied-guard discovery and cone preparation. It neither reorders nor skips any admission attempt.

Both copies share the exact input functions already computed for settled providers
and W. These BDDs are translated to CNF without further BDD evaluation. Within the
unresolved cone, all producers have Clark completion except the reading producer:
its contribution is a free choice in each copy, allowed only under its effective
guard G. Both copies satisfy G and W and must disagree on the candidate premise.
Positive self-support inside this cone is deliberately **not** refined away.
An unresolved provider outside this component currently gives `unknown`.

A concretely checked supported pair is `ruled-out`: this candidate cannot obtain
the current guarded-settlement certificate on this snapshot. UNSAT is
`not-ruled-out`, not a certificate, existence result or admission decision. The
answer applies only to that premise, reading rule, effective guard, verification
and graph snapshot. No answers are reused across snapshots or invocations.

One admission invocation has an aggregate allowance: 64 candidates
(`--sat-probe-candidate-limit`), 10,000 ms of active diagnostic time
(`--sat-probe-candidate-timeout-ms`), and 10,000,000 encoding/validation work units
(`--sat-probe-candidate-work`). The flags also enable this probe. CNF variables,
clauses and literals retain the existing per-query size ceilings; solver search
is bounded cooperatively by the remaining aggregate time. Learned clauses are not
an independently capped memory pool. Diagnostic work does not consume checker
work or condition-node allowances. Its elapsed time, including report delivery,
is excluded from the admission deadline without resetting prior checker time;
cancellation remains live. Wall-clock profiling still includes the extra work.

Counts cover candidates enumerated in reached guarded-settlement passes across
snapshots: `ruledOut`, `notRuledOut`, `unknown`, `unexamined`. Unexamined includes
allowance/cap exhaustion and candidates admission never attempts (including when
another attempt resolves their component or ordinary checking stops). It does not
count hypothetical candidates in rounds never reached. Lookahead previews are not queried: their guard may still strengthen before
iteration. Candidates only ranked, but never selected, remain unexamined.
Reused admission has no fresh candidate queries. Schema/zoo reports preserve
`candidateProbes`, including cumulative counts streamed before an interrupted run.

## Guarded settlement

After producer removal and discharge have no batch, the relevant phase can replace
a cyclic premise by a formula over globally settled atoms, under its rule's guard.
The guard stays executable. Bounds relax the reading producer to its guard so the
certificate applies before and after replacement. Earlier marks alone justify later
ones, and an unresolved external component supplies no value. Existing discharges
run first to preserve their warnings and failure-local budget behavior.

One replacement is allowed per component per snapshot. Expressions use shared
Boolean trees, without distributing conjunction/disjunction into rule variants.
A complete expression has at most 1,024 nodes and depth 64; a certificate retains
at most 8,192 expression nodes across its marks. These are optimization cutoffs:
exceeding one leaves the rule intact, reports an expansion cutoff in progress, and
is not checker exhaustion. Temporary construction, dependencies, proof storage and
traversal charge existing budgets. Real work/node/task limits retain their ordinary
stop or recoverable-skip behavior. A graph rebuild and proof installation are atomic.

Candidate-relaxed bounds are computed under G ∧ W in the premise's live backward
cone. A producer dead under its settled condition contributes no dependency edges;
its summary stays as evidence with an explicit domain-relative live/dead flag.
Temporary cones borrow the round's already-accounted summaries. They retain only
their domain and metadata, not a masked condition per producer. Iteration restricts
each contribution transiently before accumulating per-atom upper bounds and lower
guarantees, avoiding large intermediate unions outside the domain. Successful
certificates own the referenced snapshot summaries individually and retain their
conservative proof charges after the round ends. No whole old round is retained.
The reading producer is relaxed before traversal.
Before bounds, an optional deadness worklist propagates impossible settled
conditions through positive premises and kills negative premises whose atoms
are guaranteed under G ∧ W by exact producers. The reading producer's loop
premises are never inspected for this purpose. Rebuild the cone from the requested
premise; ranking, bounds and the candidate probe use the rebuilt cone. Proof
sources outside it remain separately owned and charged.

This pass indexes at most 65,536 atoms, producers and body-literal entries in total.
It reserves sixteen condition-node slots per indexed item for simultaneous
indices, queues, reasons and rebuilt metadata, plus variable-size negative-reason
vectors and BDD guarantees. These are conservative storage charges, not heap byte
measurements. Candidate preparation shares liveness tests and exact-guarantee
tests for the most recent domain D within one immutable admission snapshot. The
key includes D's exact representation; a guarantee also checks the complete
ordered exact-producer set, excluding a relaxed producer. Only the resulting
Boolean test and source IDs are retained, not the union BDD. A domain change
clears the entries. Reachability, relaxation and propagated deadness are always
computed for the candidate. No such cache crosses snapshots or program preparations.

This optional cache reserves at most `min(max_condition_nodes / 64, 65536)`
condition-node slots, including domain and map/vector metadata. Reservation is
lazy; entries that do not fit are simply not saved. Completed entries may survive
a failed candidate, but failed computations are never cached. On preparation or
pruning storage pressure, release the reservation and retry without this cache;
all spent work remains charged. The reservation makes partial-cone rollback
independent of which complete entries it added. These limits are provisional,
not a new user-facing allowance. Candidate results retain the domain, component, snapshot,
relaxed rule, rebuilt cone and reasons. A size, BDD task/node or condition-storage
cutoff discards the pass and reports the reason, retaining the original cone.
It adds no inconclusive result; global work, cancellation and deadlines propagate.
The size cap and slot estimate are provisional. This pass does not eliminate the
unrestricted bounds that run earlier, or batch replacements across rounds.

Preprocessing is lazy and charged, and has its own recoverable attempt. Candidates
with an informative guard run before unrestricted ones, then by guard node count
and immediate producer count; ties preserve the existing order. That order now
feeds a bounded lookahead of 32 prepared candidates. Prefer cones with fewer live
atoms, then fewer live producers, preserving the preceding order on ties. A cone
with at least 90% of its current unresolved component's atoms live is deferred
behind cones below that threshold. The denominator is all ground atoms in that
component at the current snapshot, not atoms visited during cone traversal; a
621/622 cone is therefore deferred. Live producer count breaks size ties only.

The window holds size metadata (charged conservatively as 16 condition slots per
entry). Optional prepared descriptors retain the domain, atom/rule IDs, live flags,
pruning metadata and sizes; current producer summaries are rebound for the chosen
attempt. Inferred guards are rediscovered. Vacant slots are refilled before choosing
again. If all 32 candidates are deferred, discovery and preparation continue beyond
that window until the first non-deferred candidate is prepared, the queue ends, or
an extra-work allowance is spent. The allowance is `max_work / 10`
charged work units per snapshot, shared across extended windows. It counts queue
work, implied-guard discovery, descriptor lookups/rebinding, failed preparations,
and their dependency/storage accounting; bounds and settlement work do not spend
it. Work before the initial window fills is charged normally, outside this extra
allowance. It is fixed before the first bounds attempt and never uses elapsed time.

The scheduler checks the allowance between queue operations, finishing an in-flight
discovery or preparation (so it may overshoot by that operation's charged work).
Spending it selects the best deferred candidate; it is not a checker exhaustion or
an unsuccessful proof, and creates no skip/negative cache entry. Deferred candidates
remain eligible in this snapshot and later ones. Global work, deadlines and
cancellation still apply inside every operation. Unexamined candidates may have
smaller cones: this is bounded lookahead, not a global sort. On preparation storage
pressure, release optional descriptors and ranking metadata, return waiting
candidates to their original queue, and retry without ranking for the remainder
of the snapshot. The window, allowance and 90% threshold are provisional; neither
changes proofs, cones or the independence requirement for batching replacements.
Progress exposes cumulative extra `lookaheadWork` and its `lookaheadLimit` alongside
the candidate; they reset per snapshot and are measurements, never cache identities.

One-hop implied guards can strengthen G before the cone is prepared. A negative
unresolved premise excludes the union of its exact producers' settled guards;
a positive one requires the union of all its producers' settled guards. Their
conjunction I is retained with the executable replacement. Original summaries
alone supply the inference; a reading producer contributes only G. The cone uses
I ∧ W. If I equals G under W, or excludes every permitted world, this increment
keeps the existing attempt with G.

Cheap producer-summary hints promote otherwise unrestricted readers. Discovery
runs only when reached, with at most one refined candidate waiting for its new
priority; others retain their ordinary priority while it waits. A candidate
selected from the lookahead reconstructs its guard independently; at most that
candidate and one waiting discovery retain inferred guards. It stops after
8,192 visited summary/body/expression units per candidate and uses the existing
1,024-node/depth-64 expression caps. BDD operations retain the existing per-operation
limits and global work charges. A most-recent signed producer union is shared
within the snapshot. Its metadata, temporary expressions, conditions and owned
source snapshots charge condition-node slots conservatively; intermediate charges
are released together after discovery. Cone preparation evicts this optional union
as well as optional bounds before retrying under storage pressure.

An inference cutoff or recoverable BDD/storage failure discards partial inference
and returns to G and its ordinary priority. Progress records `implied-guard`
attempts/skips/cutoffs. A failed inference does not itself make the fallback's
region inconclusive; subsequent proof attempts determine that result. Global
work, cancellation and deadlines propagate. Discovery is one hop, not a fixpoint,
and does not replace the preceding unrestricted bounds/removal/discharge passes.

One snapshot-local cache entry retains the latest complete bounds or failure key.
If preparing the next cone hits storage pressure, discard the optional cache and
retry preparation once under the same cap, retaining all work charges. A repeated
failure is the ordinary local skip. Reuse requires the same domain representation, cone, component, snapshot and
relaxed rule (omitted when its head is outside the cone), and pruning reasons. Metadata conservatively
uses condition-node storage slots as well as work charges. Different guards never
inherit another guard's failure. Replacing an entry releases it; successful proofs
retain their own certificates. Bound values and failed-bound keys do not cross
snapshots. Prepared cone descriptors may: complete dependencies include the reading
rule, live/dead producers, transitive pruning sources and implied-guard sources.
Every commit compares their executable shape, settled inputs and membership in the
reader's component; changed inputs invalidate the descriptor. A hit also requires
the same guard and W representations, implying the same domain without a new BDD
operation. Retry footprints additionally cover unsuccessful guard-discovery inputs,
which can become informative after a producer changes. Current snapshot/component IDs and summaries are
rebound, never copied blindly. Ranking reuses the saved live counts, with deferral
recomputed against the current component size. Original before-pruning counts
belong to the preparation that produced the descriptor.

Descriptors and complete retry footprints charge condition-node slots, and their
construction, lookup and comparison charge work. Retention is optional when it
does not fit; missing footprints use conservative reader-cone invalidation. Cone
preparation evicts descriptors along with other optional caches before retrying
on storage pressure. Descriptors are also released before downstream work, which
does not attempt guarded replacements; all metadata is released when admission ends. Repeated signed
atoms in one body need only one attempt. Progress distinguishes
`guarded-preprocessing`, `guarded-bounds` and `guarded-settlement`, with per-candidate
cone size, preprocessing/iteration elapsed time, reuse and outcome. Progress also
records whether ranking deferred the candidate, its component atom count, and its
actual bounds-attempt position (absent while it is waiting). Saved reports retain
the deferral flag even if the candidate later runs. Expression
`cutoffs` remain separate. `guarded-preprocessing`'s `reusedResult` also counts
descriptor hits within and across snapshots. Guarded replacements batch in candidate
order only when no changed reading rule occurs in another certificate's complete
proof dependencies; one replacement per rule. Dead producers count too. Batch
commit and invalidation remain atomic.
Preparation also reports domain BDD size and existing versus added condition-node
storage, including partial visited/live counts on failure. Added storage is the
amount successfully retained before cleanup, not the failed requested increment
or a byte measurement. These counters do not alter limits. Deduplicated BDD payload,
process RSS and physical footprint are separate measurements; none is inferred
from the conservative condition-node allowance.

Default warnings use the existing eight-note/sixteen-location caps, with at most
32 expression nodes rendered per formula and explicit omission counts. Full
`--verbose` evidence includes guard, settlement ranks, supporting component
rules and each implied guard's producer conditions. Inferred sources outside
the replaced premise's cone remain owned proof dependencies. Stable/supported-model oracles and fresh/cold/warm tests are correctness
gates; CLI benchmark timings and sampled memory remain measurements only.

### Structural splits

After structural reduction, shared summaries and cheap exact-cover removals, try
one whole-component search before bound removal, bound-backed discharge or
candidate-relative guarded settlement. Components keep provider-first ordering.
The domain is W; only globally settled atoms are split candidates. Reuse the
existing deadness and executable SCC scoring routines with every component atom
as a root. A leaf must be acyclic, and every live external premise must be settled.
Topological leaf evaluation uses BDDs for settled conditions, but computes no bounds.

The provisional search allowance is **100,000,000 charged work per component
attempt**, including ranking, fixed-candidate checks, pruning, scoring, leaf
computation, expression combination and certificate staging. It supplements the
existing query budget; global work, deadlines and cancellation still propagate.
Exhausting the local allowance abandons the entire attempt and continues ordinary
admission, with no partial commit. **Depth 32 and 64 leaves** are safety caps,
configurable along with the work allowance through `Limits`, the CLI's
`--max-structural-split-depth`, `--max-structural-split-leaves`,
`--max-structural-split-work`, and the matching `denotate.limits` settings.
These values participate in request/cache validity. A zero depth or leaf cap disables
the attempt; zero work leaves no search allowance. The limits apply to this
whole-component path, not the older candidate-relative case search.

Candidate scoring additionally has **1,000,000 charged work per node**, configurable
with `max_structural_split_scoring_work`, `--max-structural-split-scoring-work` and
`denotate.limits.maxStructuralSplitScoringWork`. It participates in request/cache
validity; zero disables scoring. Check the allowance between complete candidate scores; one
in-flight score can cross it and consume the remaining search allowance. It limits
further scoring, without reserving work for leaves. Total search work and global
work/BDD limits always apply. Ranking
and fixed-candidate checks count against total search work, outside this per-node scoring allowance.
There is no fixed candidate-count cap on this path. Pre-rank by the number of live
component producers mentioning the settled atom, then by the smallest selected
input-exclusivity group containing it (ungrouped last), then deterministic atom
order. Score by `(max branch cyclic atoms, sum)` with strict improvement. A perfect
score stops early; exhausting scoring keeps the best useful split already found.
Fixed conditions consume no split or scoring allowance. The older candidate-relative
case search keeps its separate policy above.
Scored branch cones and their SCC sizes may be handed to the children. One
attempt-local cache holds the best candidate's two cones and, when space allows,
the in-flight score's pair. Non-improving scores leave the best pair intact;
superseding it releases the old pair. Starting deeper scoring releases any waiting
ancestor sibling.
The selected atom and branch domains survive eviction, so children rebuild on a
miss. Superseded or non-improving candidates release their cones; consuming a cone
transfers it to the active node, and parent cone/ranking scratch is dropped before
descent. Nothing is retained across components, snapshots or sessions.

The cache uses a charged reservation of `min(max_condition_nodes / 64, 65_536)`
slots, only when available. A cone which cannot fit is dropped. The
reservation is released before staging or on failure. If it obstructs completion
(condition storage exhaustion, or a negative search after storage-limited pruning),
retry once without retention; all work remains charged against the same allowances.
This is a provisional bounded-storage policy, not a promise that retry work is free.
Progress reports cumulative cone builds/reuses/discards, liveness/pruning/SCC work,
pruning storage fallbacks and uncached retries. These measurements do not change
proof evidence or identities.

Joint expressions are interned across all leaf values and edge replacements. The
structural-split interner folds direct complementary children in conjunctions and
disjunctions, and combination reuses an identical interned branch rather than
building a conditional around it. These are structural identities over every
world, with charged traversal and temporary lookup storage. No comparison of
domain-masked leaf truths or reference back into the unresolved component is used.
The shared expression machinery for other proof paths is unchanged. The
single-premise **1,024-node/depth-64/8,192-certificate-node** caps do not apply to
this path. Work and condition storage charge construction, child references,
interning metadata, traversal, original sources, pruning evidence and staging.
Additional safety caps are **262,144 distinct expression nodes**, **expression
depth 256** and **search depth 256** (the effective depth is the smaller of this
and the configured depth). These are optional cutoffs, not semantic limits.
Projection and owned-query reconstruction preserve sharing across rules; equality,
hashing and dependency enumeration visit shared structure without expanding it.
Expression evaluation remains bounded by its certified depth and charged work.
Default expression display stays at 32 visits; requested full expression display
has an 8,192-visit safety bound and marks omitted text with an ellipsis.
Partial search/staging results are released. Original component evidence is shared
and charged once per atomic batch; per-occurrence expressions and direct evidence
remain charged separately. Direct producers are indexed once; shared certificate
size is counted once rather than traversed per occurrence. Finding replay keeps
certified positive forwarding sources and charges expansion/order of that authored
evidence DAG. Constants and multiple occurrences in one rule are valid.

A completed partition installs all its internal premise replacements together.
A local cap, BDD/storage failure or live unresolved external premise leaves the
ordinary pipeline available and adds no semantic inconclusive finding. Work is
not refunded; global work, deadline and cancellation failures propagate normally.
Cutoff attempts are remembered within this admission only, by a stable component
atom. The existing pre-commit reader closure invalidates them after changes to the
component or supporting providers/settled conditions, including upstream rewrites.
Unrelated commits keep the cutoff. No branch cache or retained session cutoff is
added, and skipping is scheduling only, never a semantic result.
Current component, scores, branch sizes, evaluation, staging, certification and immediate optional fallback reasons
appear under `structuralSplit` in progress. Default warnings name the shared proof
and replacement; full evidence expands branch evaluation and deadness reasons.

With profiling enabled, a certified joint batch also reports `replacementSizes`:
reachable expression DAG nodes across distinct signed replacement roots, and
unrestricted replacement BDD sizes separately from certificate truth restricted
to W. Totals count distinct retained BDD arrays, not semantic equivalence or solver
peak memory; maxima describe one replacement. Temporary measurement evaluates each
shared expression node once and releases non-root BDDs after their last reader.
Inspection has an independent allowance per batch:
5,000,000 work, 100,000 nodes per BDD, 1,000,000 BDD tasks per operation,
1,000,000 retained condition-node slots and a cooperative 250 ms deadline.
The defaults are diagnostic policy, not admission limits. Exhaustion reports an
incomplete measurement with unavailable totals; unexpected unavailable inputs do
not change the certificate. Cancellation still propagates. Measurement work and
BDD creation are excluded from checker receipts/counters and its elapsed time is
excluded from admission's deadline. The `structural-split-sizes` profile span and
the report's elapsed time expose the overhead. Ordinary progress does not perform
this inspection, and no measurement enters cached results or rewrite evidence.
Warning inventories can change because this pass runs before earlier proof methods.

### Case splits

After an ordinary guarded attempt is negative, or its bounds fail on a recoverable
BDD/storage limit, try binary splits over settled atoms in the executable cone's
producer premises and replacement leaves. Derived settled atoms are eligible;
unresolved component atoms are not. If no producer has a settled condition varying
inside the current domain, skip this search and preserve the cached bounds without
constructing a scoring graph. Ordinary unsplit successes
retain priority. Release the optional broad-domain bounds before branch work.

Provisional cutoffs are **16 scored candidates per tree node, depth 3 and 8
leaves**. Candidate order is deterministic ground-atom order. Conditions fixed by
the current domain are discarded before scoring, without consuming depth or
leaves. Rank by `(maximum branch cyclic atoms, sum of branch cyclic atoms)`,
strictly improving on `(N, 2N)` for the parent. SCCs include positive cycles and
self-loops; polarity is not a proof. A score of `(0, 0)` is optimal and stops the
scan, retaining the first candidate on ties. Otherwise exhausting the scoring cap
abandons that node, as do depth/leaf or complete-expression/certificate cutoffs.
No incomplete tree installs a replacement or becomes a checker-limit finding.

Every live branch prepares and prunes its own relaxed cone and computes its own
bounds. Exact guarantees may seed true constant branch answers; false bounds seed
false ones. The complete expression and all leaf steps share the existing
1,024-node/depth-64 expression and 8,192-node certificate caps. No branch uses
negative-result or bounds caches keyed only by rule/occurrence. Successful trees
own and charge every leaf certificate; partial trees and scoring graphs are
released. A failed local bounds operation can trigger a narrower split; exhausted
global work, deadlines and cancellation stop normally. Spent work stays charged.

Scoring charges traversal, BDD tests and SCC work. Temporary graph storage reserves
eight condition-node slots per atom and two per dependency, in addition to the
ordinary cone, candidate and domain storage. These are conservative bookkeeping
slots, not bytes. Retry metadata includes the component's producers; committed
proof dependencies use the union of the actual branch certificates and implied
guards. A conflict in any branch prevents batching.

Progress reports candidates scored, fixed candidates bypassed, cutoffs, chosen
atom, parent/branch cyclic sizes, current and maximum depth, leaves, and each
branch's prepared/live atom counts. Default warning notes name the split atoms
and combined replacement; full evidence labels each branch and its settlement
steps. Public finding identities stay `(verification, source rule, occurrence)`.
Multi-way splits, branch memoization and conditional schedules remain deferred.

## Re-scoring

Deadline polling reads the monotonic clock on the first charge and every 256
charges thereafter. Explicit operation/phase checks and zero-work charges always
read it immediately; cancellation is still checked on every charge and boundary.
Boolean operand/result validation, preflight completion and failed result
construction are explicit boundaries, so repeated recoverable BDD failures do not
wait for the charge counter to poll the deadline.
At most 255 charge opportunities skip a clock read. This is not a wall-clock
latency bound: one BDD operation or other work item can take arbitrarily long
between opportunities. Work accounting, deterministic limits and cached receipts
are unchanged. Diagnostic-time exclusion keeps its existing separate clock policy.

Admission progress in CLI stderr and the `.den` editor reports round/stage,
unresolved ground components, affected atoms, current component and committed
rewrites, with a precise final update on exhaustion. It uses existing graph
metadata, not extra admission or BDD work. Inner observations are separate from
the optional memory-profile span stream; both can be enabled together. See the
[progress protocol](../crates/den-lsp/PROTOCOL.md#checking-progress-and-logs).
They do not alter deterministic allowances, cache keys or results. As with other
logging, delivery costs wall time; deadlines remain cooperative.
After admission, progress lists remaining component sizes and bounded cycle
excerpts. Checking then reports the current target and operation, with exhaustion
as soon as it is detected or restored from cache. Recoverable query failures allow
other checks; deadlines ordinarily stop the verification, except for advisory
notices and optional attribution. This changes observation only, not resource
allowances or the existing recovery policy. Finished CLI verification reports are
flushed before later verification work.

Admission prioritizes unresolved negative components and their blocked providers
(phase `relevant`). Only after that work reaches a fixed point does phase
`downstream` attempt removals on other still-blocked heads and discharge redundant
input negations on settled rules. The latter also runs without cycles when selected
assumptions can justify warnings. Each phase keeps the existing structural,
exact-coverage, strengthened-bound, discharge, then guarded-settlement ordering. Relevance is recomputed
after commits. Targets and support differ: proofs keep all providers they need,
including settled components, while unrelated structural worklists, evaluation and
summaries wait. Graph maintenance and the full input universe/W remain shared;
proof conditions retain the original variable order and universe for replay.

Phase A exhaustion retains the ordinary admission limit. Global/shared logical
exhaustion in phase B instead sets `downstream_incomplete`, with phase/resource details, and
leaves cycle admission classifications intact. It produces an Information diagnostic
at the verification and an optional summary field; it does not change verdicts or
exit codes. Same-context admission reuse retains this marker and its receipt under
the same logical limits. Deadlines/cancellation still abort and are never cached.
Phase B has no new allowance: both phases share the existing budget. Committed
batches survive exhaustion; pending batches remain transactional.

Ordering can remove warnings: a downstream producer that becomes exact after a
cycle is resolved is no longer a removal target. Preserving those warnings would
require a separate lint policy. Existing finding identities and proof rules stay
unchanged; each migration records the observed warning differences.

Admission starts with a `structural` pass over blocked regions (negative cycles
and their dependents); an already admitted graph has no structural targets.
It reaches a worklist fixed point before committing deletions and running any BDD
proof. After BDD rewrites have admitted an unrestricted program, the existing early
exit avoids another optional round. Truth/falsehood propagation reads current
rule bodies, head producer counts and already settled fixed boundaries; it never
builds a Boolean context. The existing concrete evaluator supplies input-free,
already settled boundaries, including positive recursion, so folded and unfolded
preparation agree. This private dependency-closed evaluation does not select or
validate an input world. Components with discharged premises are excluded from
that evaluation to avoid BDD replay work; propagation can still use their current
bodies. No new unfounded-set or positive-cycle inference is added to blocked regions.

Subsumption expands only positive, single-producer premises. Comparisons stop at
32 expansion levels or 128 visited literals; a cyclic expansion is skipped.
These are optimization cutoffs: skipping a comparison yields no rewrite, not an
inconclusive verdict. Within one head visit, normalized bodies are ordered by size
and deterministic rule order. Exact duplicates use a map; subset searches index
retained bodies by their first signed premise and inspect at most 64 candidates.
For N producers and bounded expansion size K, a visit costs
O(N K log N + N K² + 64 N K log K), rather than an unbounded N² pair scan.
The index can miss a valid subsumption beyond its candidate cutoff. Changes to
producers or structural facts invalidate their reader closure, so a head can be
visited again; the whole pass is still bounded by the ordinary work/deadline limits.
Indexing, propagation, expansion, comparisons, certificate storage and graph commit
are charged. Global exhaustion publishes no partial structural batch. No BDD
condition allowance is consumed by structural certificates.

Structural evidence is a shared flat DAG per pass, trimmed to facts and rules
needed by actual removals. Fixed-boundary source chains are collected lazily from
the retained fixed graph, with charged traversal. Settled helpers may simplify
privately to justify a blocked removal, but their rules are never committed as
removals or warnings by this pass. Warnings preserve per-source-rule instance coverage and
identify supporting/unfolded rules at current locations. Settling chains are not
copied into every retained proof. Ordinary presentation and internal structural
rewrite evidence keys use only direct settling/unfolding support, including
settled premises needed for subsumption. The transitive certificate is traversed
only on explicit request (`check-den --verbose`); that traversal can revisit shared
support across proofs. Symbolic evidence and keys are unchanged. Local session
inputs still close original dependencies, including transitive support; direct
evidence keys do not replace that invalidation boundary.

Per source warning, default presentation retains at most eight distinct structural
or bound-removal notes and sixteen related locations, after provenance union, with exact
omission counts. Notes use lexical order; retained locations use immutable source
span/label order. Legacy symbolic coverage/discharge locations remain unbounded and
are protected in mixed warnings. Full detail removes these display caps. These are
presentation policies, not checker budgets: proof coverage, verdicts, limits and
`data.finding` identities are unchanged. Coordinate indexes and source hashes are
reused per immutable snapshot within presentation/export; columns still scan the
containing line, so extremely long lines retain a linear per-column cost.
The `admission-structural` profile span is separate from BDD result-node
traffic and retained-condition snapshots.

Within each admission snapshot, producer removal runs before negation discharge.
A nonempty removal batch rebuilds the graph and starts a fresh snapshot; cycle
bounds run only after removals reach a fixed point. The coverage proof and
transactional commit rules are unchanged. This can reduce BDD work and preserve
useful progress before later exhaustion, but changes work charges and may require
extra snapshots. Symbolic evaluation covers the selected provider cone; summary
construction keeps only the complete producer groups later proof stages read.
No new allowance is introduced; `admission-candidates` profiling
covers the proof passes. Progress distinguishes `producer-removals`,
`guaranteed-bounds`, `bound-removals` and discharge `candidates`/`upper-bounds`.

After shared evaluation and summaries, removal, bound-removal and discharge passes
visit target components by upstream level (non-target providers transmit levels),
then by atom count and deterministic graph order. A successful component batch
commits before another component or tier runs. The next round rebuilds the schedule;
component IDs do not survive a commit. This can cost more graph rebuilds than a
global batch, but preserves completed upstream work if a later component exhausts.
Within each component, rule order and proof criteria are unchanged. Earlier
settlement can make a later rewrite unnecessary, so warning sets can change.
Guarded candidates use the same provider-first ordering of their components,
then the existing guard/cone ranking within each component. Each component gets
up to **four bounds candidates per turn** before the next waiting component runs;
after the last component, the first resumes its remaining queue. A lone component
continues without a switch. Four is provisional: it permits small independent
batches while limiting how many attempts delay another component. A successful
batch commits before crossing a component boundary. Independent readers within
the same component can still share a batch.

Turn slots count actual bounds-candidate positions, including reused bounds and
local failures. Cached-negative lookups and preprocessing do not consume slots.
Each component keeps its ranking window and at most one waiting inferred guard,
charged to existing storage. The extended-lookahead work allowance remains shared
across the whole snapshot, not renewed per turn. Optional ranks and saved inferred
guards in waiting queues can be evicted on storage pressure, returning candidates
for ranking or guard discovery; this never discards a proof. The temporary bounds cache still has
one entry shared across components. Progress positions remain global to the
guarded pass and reveal the component order and resumption.

If a component's pass runs out of condition storage outside the existing narrower
attempt recovery, its temporary coverage/bounds and pending proofs are dropped
before restoring the saved storage count. Shared summaries, prepared entries and
committed proofs are not released; work is never refunded. A `component-storage`
skip suppresses that component's later passes and guarded candidates until its
dependency inputs change. Retry follows the pre-commit reader cone through either
polarity, including old SCC members. Completed admission can reuse these explicit
skips, as with other local failures. A guarded certificate's retention failure is
likewise local to its attempt, preserving earlier independent certificates.
Shared preparation storage, global work, deadlines and cancellation still stop
the phase. No allowance or within-attempt yield is added: a single operation or a
long preprocessing sequence can still spend the global work allowance. Enforced
work sharing remains separate work.

After cheap removals have no batch to commit, a recursive component with a
non-exact candidate and exact head coverage can use strengthened bounds. Its lower
guarantees are unions of existing exact producers only. Upper bounds descend from
true, restricting internal negative premises by the complement of those guarantees.
A candidate is redundant when its complete body's upper bound is covered by the
head's exact producers under W. These exact producers remain in the graph; no
recursive lower cover or new settled meaning is inferred. Supported-model upper
bounds, including positive self-support, remain the contract. Bound removals commit
before discharge, so later snapshots can expose further exact producers.

Guaranteed bounds are computed once per eligible component in the snapshot and
released after its last candidate. Their producer summaries, guarantee unions,
old/new bound maps and retained proof conditions charge existing work/storage
limits. A successful proof retains its component certificate through an `Arc`,
conservatively charged per proof as for discharge certificates; covering summaries
are still cloned. Default evidence shows exact head-cover producers, with the same
per-warning display caps as structural evidence; full component support is expanded
on request. This can retain substantial metadata in a large component and is not a
memory optimization. An unsuccessful strengthened pass may be followed by legacy
discharge bounds. Neither computation nor its temporary cache crosses snapshots.

Within one immutable admission snapshot, the removal pass computes a head's union
of exact producers only when its first non-exact candidate needs it. Subsequent
candidates reuse that condition and the same ordered producer list. The temporary
union is charged to `max_condition_nodes` while retained, including its accumulator
during construction, and its cache entry is released after the head's last
candidate. The temporary cache never crosses snapshot or verification boundaries;
candidate order and proof policy stay unchanged. This avoids repeated BDD unions
without changing symbolic evaluation or upper-bound iteration. Each successful
removal still clones covering producer summaries into its proof, so evidence
storage can remain quadratic. BDD result-node traffic and retained-node snapshots
do not measure that metadata storage.

Local query construction builds one borrowed head index for original producers and
rewrite proofs on the first query of each verification invocation. Original closure
then visits reached heads with a worklist, rather than rescanning every rule and
proof until no dependencies change. Discharge-context projection reuses the reached
proof keys. The `LocalInput` value, cache identity and logical receipts are unchanged.
Index storage is physical graph metadata, O(original rules + proofs), released after
the local queries; it is not session retention or BDD condition storage and adds no
new limit. Process memory profiling includes it, and `LocalMetrics.keys` includes
construction on the first query. Constraint/domain filtering and the global input
universe required by discharge completion are unchanged. Emptiness and coverage
do not use this local-input path.
The up-front index can cost more than filtered scans for a single tiny query in a
large program; there is no size-based bypass heuristic. Measure that setup cost
alongside the savings from repeated queries and deeper original closures.

Admission recovers from per-operation BDD task/node failures inside individual
proof attempts: exact-producer coverage, a removal check, component bounds,
guaranteed bounds, a bound-removal check, or a discharge check. Failed temporary
conditions and their retained-node accounting are released. Work stays consumed:
a failed condition preflight is charged its task
allowance plus one stopping step, with no construction charge. The bound is still
`min(max_bdd_tasks, remaining_work / 2)`; when remaining work is the tighter bound
or ties it, failure reports `BDD preflight: work` and stops admission. Successful
operation charges are unchanged. Completion-equation preflights are unchanged.

Temporary upper/guaranteed/guarded bounds, guarded-cone preprocessing and guarded
certificate retention also recover from condition-node storage exhaustion,
releasing their partial values. Escaping component-pass failures use the owned
batch boundary described above. Neither recovery applies to shared context setup or
transactional graph installation, nor raises the storage cap. Earlier global work remains charged, so a
later unrestricted bound can still exhaust work before another guarded attempt.

Positive recursive evaluation uses deterministic sparse rounds. Every producer is
visited initially; a changed atom schedules its readers, including replacement
expression dependencies. Later readers run in the current round, earlier readers
in the next, preserving the original producer order among scheduled rules. External
premises are already settled and internal dependencies are positive, so omitting
unchanged bodies preserves the least fixpoint. This removes repeated whole-SCC
scans on sparse propagation, not the cost of genuinely growing conditions.

The invocation-local reverse index and current/next queues reserve three logical
condition slots per rule, two per indexed atom, and one per internal dependency. Construction and
notifications charge work. If the reservation cannot fit, retain full scans. If a
condition later exhausts storage while that reservation exists, drop the worklist
and restart from bottom with full scans before declaring any new head unknown.
Consumed work is not refunded; global work, deadlines and cancellation still stop
evaluation. No limit is raised. A completed component releases its scheduling
reservation; nothing is cached across graphs.

Individual atom evaluation also recovers from per-operation BDD node/task and
condition-storage exhaustion. The exhausted head becomes unknown for this
snapshot. Its positive component restarts from bottom, releasing all partial
conditions in that component and retaining the failed heads as opaque. Work is
not refunded, including restart scans. A false conjunct or true alternative may
still decide a reader; otherwise it becomes unknown too. This deliberately does
not retain partial lower bounds or evaluate under individual readers' guards.
Admission summaries omit unknown premises just as they omit blocked ones: they
cannot become guarantees. New snapshots retry evaluation; owned local query
results retain unknown atoms and their originating causes by semantic key.

Admission's symbolic retention frontier includes the premises and replacement
leaves of every required producer summary. Required groups contain all producers
in target components, plus complete one-hop producer sets for cyclic implied-guard
discovery. Earlier provider layers are evaluated but their conditions are released
after the last consuming component finishes. A positive recursive component keeps
its providers through every restart. Missing sparse facts still mean false;
explicitly released values instead cause an internal error if read. The deterministic
last-reader schedule, sentinels and summary membership use charged work and storage.
Committed proofs, prepared caches and frontier metadata reserve space while symbolic
evaluation runs; no needed value is evicted. Checking keeps its existing retention.

Summary BDD task/node or condition-storage exhaustion is local to a complete
producer group. The partial group is dropped, storage accounting restored, and
every target component that needs it receives a `summary-storage` skip. All its
passes, including structural splits, wait for dependency invalidation. Complete
groups needed only by skipped consumers are released; partial sets never supply
coverage or implied guards. Work is not refunded. Independent components and prior
commits remain available. Skips accompany same-context admission reuse and are
invalidated through the pre-commit reader graph; component IDs are never cached.
Unused upstream summaries no longer cause downstream-incomplete notices.

Failures in shared context setup or frontier bookkeeping, total work limits and other
retained-storage limits stop the current phase, with the separate downstream marker described above.
Deadlines and cancellation still abort the whole invocation. No pending batch
is salvaged on these failures. Local skips allow independent proofs to commit.
Retry tracking uses ground identities stable within the preparation, not changing
component handles. Bounds, bound removals and discharge keep conservative
invalidation: any rewritten head in their old dependency cone invalidates them,
through either sign and even
when an SCC splits. Coverage and removal use a narrower comparison after the
prospective graph rebuild. Coverage retries when an exact producer enters or leaves,
its settled body changes, or a previously settled head is rewritten in its premise
cone. Removal also retries when its own settled premises change. Rewriting a blocked
premise that stays blocked does not change the summary condition. Comparing current
bodies catches input-guard discharge even when the producer's rule ID is unchanged.

A single scan shares coverage-change detection across failed attempts for each head;
there is no per-candidate copy of its wide producer set. Reader closures are built
only when needed, from pre-commit edges. Metadata work is O(rules + dependencies +
visited premises + skipped attempts), apart from ordered-map/set lookup costs. It
is charged and can stop admission globally before the commit. Unchanged skips keep
their original reason and consumed work; neither graph nor retry invalidation is
partially published if the rebuild or comparison exhausts. No retry cache crosses
preparations. Retry footprints retain rule IDs; the separate prepared-cone cache
also retains its domain condition.

Completed negative producer-removal, bound-removal and discharge attempts are
also remembered for this admission invocation. They follow the same invalidation
rules as skips; conservative cone changes can retry bounds/discharge even if the
computed conditions would be equal. Cache lookup costs one work step. Cache
invalidation is charged as above, now including remembered negatives. Entries hold
an attempt identity and head, with bounded observational history when progress
is enabled. Guarded attempts with a complete cone additionally retain its complete
producer footprint; other attempts use the conservative reader closure. Whole-component
computations still retry after any change in their component.
Obsolete attempts are removed and all metadata is released when admission ends.
Negatives never become skip records, exhaustion counts or inconclusive findings.

The negative lookup precedes per-head coverage and component bounds, so no such
prerequisite is built solely for cached consumers. Shared symbolic evaluation and
summaries still run each round. Profiling/progress aggregate run reasons, outcomes
and elapsed time per attempt kind and round; coverage/bounds time is separate from
proof operations and from symbolic/summary time. These observations do not enter
receipts or retained checking results. Finer skip invalidation and retaining
successful intermediate conditions across rounds remain separate measured work.
Saving work can improve bounded outcomes; cache bookkeeping can also cost work
when little is reused. Compare complete runs for proof/diagnostic equality and
review constrained-limit differences against semantic oracles, rather than
requiring identical exhausted paths or receipts.

Admission preserves input variables and their prepared order, selected W and limits.
Unchanged summary operands repeat the same BDD work, while the available preflight
allowance can only decrease. Input/order changes defensively invalidate all skips.
The invariant and the outside-W guard case are recorded in [decisions](decisions.md).

Outstanding skip records travel with the admitted graph and survive shared
admission reuse. Reporting projects current semantic keys and locations. Only skips
whose target lies in a remaining negative component make that region's admission
inconclusive; downstream skips do not contaminate upstream regions. Global summary
skip records are advisory and do not revoke admission achieved by other proofs.
Progress counts all failed attempts, including those invalidated and retried later.
The current record set can therefore be smaller than the progress count.

Concrete replay looks up discharge proofs in a map keyed by ground rule instance
and literal occurrence, maintained with the rewrite proofs on both admission and
local-runtime installation. The map holds only proof IDs and is empty when all
rewrites are producer removals. Lookup is logarithmic in the number of discharged
premises, replacing an uncharged scan over every rewrite proof for each replayed
literal. It adds O(discharged premises) physical metadata, with no new allowance,
semantic key or cached query input; deterministic charges and receipts are unchanged.
Condition-context construction in discharge validation and charged proof scans
remain unchanged. Reusing those requires a separate accounting decision.

### Memory profiling

Phase progress from `check-den` and the `.den` editor includes best-effort process
memory readings. RSS and physical footprint are separate OS metrics; their peak
fields are process lifetime high waters, not peaks attributable to the last phase.
Unavailable readings are `null` (RSS on macOS/Linux, physical footprint on macOS).
These include all live work in the process and are distinct from cache accounting.

```sh
just check-den path/to/program --profile-memory /tmp/den-memory.jsonl
just bench-den-memory --items 1000 --inputs 1000 --width 4 --warm
just bench-den-memory --items 1000 --inputs 1000 --width 32
```

`--profile-memory` creates a new file and streams JSON lines, including starts of
unfinished stages. It works with `--no-progress` and does not change stdout or exit
policy. The optional profiler samples memory every 20 ms while spans are active;
`sampledPeak.rssBytes` and `sampledPeak.footprintBytes` are maxima of boundary and
periodic samples, lower bounds on true phase peaks. The `peak*` fields remain OS
lifetime high waters. Nested spans overlap: their durations and peak sizes must not
be summed. An `end` event means the scope exited, including on failure; the CLI
outcome determines success. Write failures in the profile stream are best-effort.

The CLI buffers JSONL in 64 KiB, flushing every 256 records or every 250 ms
(including idle periods), at phase/span boundaries, and on return or unwinding.
On Unix, SIGINT/SIGTERM request a flush from the writer thread, then restore and
re-raise the signal; the signal handler performs no IO or locking. SIGKILL cannot
flush: up to 256 pending/in-flight records may be lost, and recovery ignores a
partial final line. Flush intervals depend on OS scheduling and successful IO;
this is bounded buffering, not durable storage. Admission ranking and intermediate
split updates use the existing 250 ms delivery throttle. Attempt starts/ends,
chosen splits, cutoffs, failures and final summaries remain immediate; counts are
updated even when an intermediate event is suppressed.

`peakAccountedConditionNodes` is the maximum accepted condition-storage accounting
observed within a span, excluding rejected demands. It is a peak of the checker's
individual accounting pools, not their sum, physical BDD live storage or heap
bytes. Nested spans observe the same events. The zoo reports this maximum beside
cumulative `bddResultNodes` for each phase; neither is a timing or memory golden.

Stages separate fixed runtime reconstruction, evaluation, export and binding;
residual preparation, including `grounding` and `graph-and-components`;
`input-key-order` and semantic-key construction; each admission round's symbolic,
summary, candidate and commit work. Key projection reads the current ground graph
on demand; there is no longer an `admission-key-refresh` stage. `bddResults`,
`bddResultNodes` and `bddResultNodeBytes` count new wrapped BDD results produced within a span.
They are cumulative result payload, **not** allocator traffic or simultaneous live
storage, and exclude the BDD library's internal temporary allocations. Retained BDD
snapshots at symbolic, summary and candidate boundaries deduplicate `Arc` sharing and report
occupied node payload; vector capacity, maps and allocator overhead are excluded.
Profile-only admission `storage` events split these snapshots into symbolic values,
summaries, committed proofs and optional prepared caches, alongside
each pool's accounted nodes. They include kept/released condition and unknown-atom
counts plus frontier metadata. Arrays can be shared between pools, so their actual
node counts must not be added. These are boundary snapshots, not peak live BDD
memory; use the round's `peakAccountedConditionNodes` and sampled process memory
alongside them. Ordinary progress does not scan BDD storage for these reports.
The committed-proof pool traverses each shared joint certificate once and uses
the checker's installed-evidence accounting. Round-only symbolic values and
summaries are dropped before graph commit; a post-commit snapshot reports the
remaining proof and cache pools.
`Condition` clones share storage; independently computed BDD arrays do not share
their nodes. Memory samples are needed alongside these counters.

The companion benchmark has positive recursion, fixed false producers, four-way
joins, multiple inputs and residual negative cycles discharged during admission.
`--items`, `--inputs`, `--width` (inputs per item), `--layers` (fixed layers), and
`--verifications` vary its shape. Around 30,000 items, 29,000 inputs, width 1 and
28 layers produce roughly three million atoms, mostly fixed. Start smaller: this
is a configurable reproduction tool, not a promise that the full size fits memory.
Its logical limits are explicitly reported (defaults times 100), with a configurable
operation timeout. `--unfolded` and `--no-retention` are separate fresh-process
controls. `--warm` reloads the same source with the session retained and compares
outcomes. `--findings` adds a violation derived through fixed rules; presentation
runs for every verification. Measure through the complete run, since key projection
also serves cache inputs and findings. Profile one process at a time; allocator
retention and profiling overhead
affect observations. No default checking policy changes, timing or memory goldens.

The `.den` CLI additionally writes `type: "progress"` records with its existing
structured phase/admission observations, including sizes before and after admission,
and a terminal `type: "run-end"` record with the checker exit code and optional error.
These are additive record types; the fields of `type: "profile"` are unchanged.
No terminal event means completion was not observed, not success. `--no-progress`
suppresses human stderr output while keeping these profile observations.

`just bench-den-schema` uses the actual CLI and a synthetic Shipping News format
tree, rather than session APIs. It shares the `profiling` build between sampled and
ordinary runs and never raises limits implicitly. Sources, effective configuration,
partial logs and reports are retained even for exhaustion or process termination.
See the [schema benchmark](../crates/ir-text/examples/schema/README.md) for its
explicit semantics, small oracle-checked presets and production-scale target.

### Outcome scorecards

```sh
just score-den path/to/program/den.root \
    --edit path/to/edited-program --json /tmp/den-scorecard.json
just score-test-dsl path/to/program.testdsl \
    --edit path/to/edited.testdsl --json /tmp/test-dsl-scorecard.json
```

Only the first root/file is required. `.den` accepts a folder or `den.root`, runs
all explicit verifications through the same request API as `check-den`, and omits
edit measurements unless `--edit` supplies another root. The test DSL command
retains its labeled fallback edit: it appends an unrelated mapping. Supply a real
edit for meaningful edit numbers.

Both commands support `--samples N` (default 5, after one discarded warm-up),
`--timeout-ms N` (default 60,000 per operation), and `--unconstrained` (lifts session
retention limits only; fresh-local remains uncached). Run them alone for useful
timings. The logical limits remain the checker defaults, and `.den` reports the
effective limits and retention configuration in JSON. The scorecards compare global
BDD, fresh local BDD, cached BDD, optional relation-SCC grounding, and controls for
planning and grounding reuse. General assumptions force global verification even
in a session; the `.den` report labels that fallback. Preparation reuse may still
apply, but the variant's name does not imply verdict-cache reuse.

The `.den` scorecard additionally compares `folded-bdd`, the retained preparation
path used by editors. It includes keyed fold projection/binding, with retained fold
reuse on warm/edit runs when the fixed projection is unchanged and retention is enabled.
Samples are still per verification, so they do not amortize preparation/admission
across other verifications. Existing variants remain unfolded controls; the test
DSL variants are unchanged. `preparation_cache.fixed` reports cumulative executed,
reused queries and retained bytes; bypass counts only direct preparations with
retention disabled. The human report also shows accounted retained fold bytes.

Use `just bench-den-fixed 4000 4` for an abstract mostly-fixed workload comparing
unfolded execution with cold and warm folded runs across four verifications. Within
a folded run, each distinct restriction selection prepares and admits once; groups
and results remain per verification. The benchmark asserts outcome agreement and
reports timings and retained sizes, never timing goldens. It also reloads an edit
to an input-dependent rule to measure fixed-query reuse. Add `--ground-assumption`
after the counts to include ground validation and its early fixed/residual preparation,
timed together and shared with all requests; `--two-selections` alternates two restriction sets and
`--no-retention` measures direct fixed preparation. The
scorecard's direct API timer instead includes lazy ground validation when needed.

The one-shot CLI uses direct fixed preparation, avoiding portable export and
binding while still sharing preparation/admission within its invocation. Editors
retain the session fold; the scorecard keeps its retained/direct controls.

Fold retention uses one Salsa query for the entire fixed cone, with no byte cap.
The session keeps every completed fold under the checker limits and replaces the
previous value when its inputs change. Other cache budgets are unaffected. The old
quarter-of-session allowance made an already-computed fold pay reconstruction and
export costs repeatedly once it outgrew that pool. Checker limits bound work and
atom/rule counts; the retained bytes are accounted separately, not claimed to be a
heap or RSS ceiling.

`Retention::max_entries == 0` disables fold retention. That path calls direct fixed
preparation on the current corpus, avoiding reconstruction/export altogether.
`max_bytes` alone applies only to the other pools. Outcomes agree between retained
and direct preparation; producer/witness choices and transfer receipts may differ.
Reset, value eviction and failed/interrupted fold preparation release the value.

The query input excludes input-dependent rules, but a fixed edit recomputes the
cone; per-relation SCC reuse is not implemented. The retained value stores original
instance substitutions and true producers, not duplicate grounded rule bodies.
Cold reconstruction/export and warm source binding still have costs; re-score them
on real programs. Original validation, eligibility, residual grounding and admission
remain fresh across snapshots. Checker ceilings and admission semantics are unchanged.

### `.den` measurements

Each sample and variant starts fresh for each verification, then reuses that session
through cold → warm → edit. Warm reloads the same sources with an added comment into
a fresh corpus. Declaration matching uses semantic keys, so file moves do not change
identity. Added verifications have only edit measurements; removed ones have no edit.
Roots without verifications are **unconfigured**, and unselected obligations are
listed. A consistent verification with neither obligations nor notices is a
consistency-only result; a selection containing only notices is labeled separately.

The human table gives median milliseconds and maximum BDD observations across samples.
`--json FILE` also retains every sample, size, outcome, comparison and cache counter.
Checker timing has four non-overlapping phases:

- **Preparation:** including selected-assumption evaluation and source-schema/group indexing.
- **Admission:** admission rewrites; keyed content uses the current graph without rebuilding.
- **Checking:** verification, replay, attribution and session bookkeeping, minus the
  notice pass. `verification_call_ns` records that enclosing call: checking plus
  notices, not an additional phase.
- **Notices:** the actual selected-notice pass inside verification, run once.

Loading, rendering, size inspection and fresh-control runs are outside those timings.
Unreached phases and a missing notice pass are `null`, not zero. Sizes are sampled
after preparation, before admission rewrites: input atoms, ground atoms, rule instances,
components and the largest five by atoms then rules. Counts of selected assumptions,
obligations and notices are included separately. No parser or LSP latency is measured.

The additional `size.fold` reports present/absent fixed facts, retained evidence
atoms/rule instances/components/dependencies, and residual atoms/rule instances/
components. The existing size fields include both parts. The fixed evidence is
currently the full original settled graph plus one derivation per true fact,
shared within the run; it is not a compact proof store or a heap measurement.
Residual grounding still seeds fixed possible tuples to preserve rule and finding
identity, including false guards. Graph indexes are shared within a restriction
selection; group indexes remain per request. This step
reduces repeated executable and symbolic work, not all initial grounding or evidence
storage. Program-level validation is outside the scorecard's phase timers. When a
cone needs grounding it now includes the fixed fold and residual preparation; later
requests reuse both. The CLI memory profile reports the nested `fixed-evaluation`,
`residual-preparation` and `assumption-specialization` spans. Compare total preparation
and overall peak footprint, not validation time alone or sums of nested spans.

Validation and W share one view specialized by exact fixed truth. The original
residual remains for admission/evidence; the specialized view retains its own residual
rules and dependency graph, sharing fixed evidence. Both are run-scoped. The fold
has its own allowance. Residual grounding, ground-atom propagation and cycle indexing
now have separate allowances (`Limits` for each) and receipts:
`ResidualPreparation` depends on `FixedFacts`, `SettledAtoms` on the residual,
and `AssumptionValidation` on settlement. SAT encoding preparation depends on
settlement and, when needed, validation. The propagation worklist charges atoms,
producers, premise visits and graph reconstruction; no repeated full rule scan is
needed for each new value. Supporting reasons use original instance IDs and premise
positions, not expanded transitive proof copies. Request attachment and W remain charged to preparation.
Default ceilings are unchanged. Exhaustion is inconclusive and interruption does not
install partial preparation. Direct and optional relation-cache requests requiring
ground validation use this same fold; other direct requests remain unfolded controls.
There is no cross-edit validation cache, even when a session reuses the fixed fold.

BDD figures have distinct meanings:

- `max_per_query_bdd_nodes` is the maximum logical BDD-size observation in the
  available receipts, not a simultaneous memory peak.
- `max_per_query_retained_condition_nodes` is the maximum logical retained-condition
  observation for a query. Shared conditions can be counted conservatively.
- `cache.retained_condition_nodes` counts payload retained in the session's local
  cache after verification. Cache byte counts are also conservative payload accounting,
  not measured heap usage or RSS. Planning, grounding and fixed folding have separate retained bytes.

Receipts may describe reused work and include rejected attempts. These figures are
neither fresh allocation counts nor sums presented as memory peaks. Missing observations
remain `null`. Plan, grounding and local-cache statistics expose execution, reuse,
eviction, bypass and retention, with their internal timing counters. Those counters are
subsets of the checker phases, not extra time to add to the total.

Each authored obligation is counted once by kind and verdict, including implicit
trivial uniqueness proofs. Its components and findings are separate: `exactly_one`
can have both a coverage and a uniqueness failure. A known failure remains visible
when checking is incomplete; coverage and emptiness counts are then lower bounds.
Unsupported and no-meaning region counts can overlap. Notices are counted by state
and never become obligation failures. Inconclusive outcomes include phase and resource.
Statistics do not enumerate uniqueness's Cartesian grouping domain; an overflowing
group-total count is `null`, with the verdict still derived from the queried groups.

Comparisons use keyed obligation/component, uniqueness-group, region and notice
outcomes, excluding witnesses. Cold controls warm; an edit also gets a fresh control
of the same variant. Global BDD is an additional fresh control for each snapshot.
Same-path mismatches, conclusive contradictions across paths and operational errors
fail the command. Cross-path differences without a contradiction remain visible in
JSON; unsupported/incomplete runs are never speed wins. Ordinary findings do not fail
the scorecard command: it measures them. Use `check-den` for diagnostics and checking
exit codes.

Run private programs and inspect results in their own work environment. Output uses
ordinary names and paths and is **not an anonymised export**. Bring feature requests
and deliberately abstracted reproductions elsewhere, rather than raw results. The
scorecard does not embed full sources, diagnostic messages or witnesses; diagnostic
quality remains the job of `check-den`.

The existing test DSL scorecard additionally measures lowering reuse and retains its
historical detailed result output and comparison rules.

## Editor latency smoke

```sh
just bench-lsp
```

Real LSP round trips at three program sizes, with no timing thresholds.

## General assumption evaluation

General selected cardinality restrictions are evaluated independently during
preparation, under the existing work, grouping, BDD and retained-condition limits.
An incomplete W is never installed. Its consistency is checked before admission.
Independent symbolic evaluation covers the union of the selected restriction
relations' ground dependency cones, in the independently specialized view when
needed. It keeps the whole program's input-variable universe and chosen order:
cone selection limits evaluation, not the inputs represented by W. No selected
restriction establishes its own meaning. Cone indexing and traversal use the
existing work and cancellation limits; exhaustion remains inconclusive. Group
enumeration still includes domain-defined coverage groups with no producer.
Whole-program admission, findings and checking follow as before.

This avoids evaluating unrelated positive components before W exists. The
knowledge-form 7×7 ring demonstrated that cost: independent evaluation exhausted
its deadline while the same input restrictions alone built a small W. This change
does not promise cheap whole-program checking afterward.

Local verdict caching remains enabled for input-only at-most-one contexts without
input cardinality declarations. General
constraints invalidate the absent-extension argument for projecting W into a local
query. Their verdicts are recomputed; grounding and plan reuse remain available.
A future optimization must retain or correctly quantify every external constraint
input and preserve cold/warm results, replay, consistency and cancellation behavior.

## Verification evaluation within W

`CheckRequest::checking_within_w` is opt-in and defaults to false. The CLI flag is
`--checking-within-w`; the editor setting is `denotate.checkingWithinW`. Once
assumptions and admission are established, enabled whole-program verification,
notices and the local path's coverage/emptiness pass evaluate exact conditions
masked by W. Default checking, public symbolic APIs, admission, rewrite proofs
and W construction remain independent of this option; their conditions are exact
throughout the declared input universe U, using component masks when declared. Cached local uniqueness/no-meaning evaluation
also remains unrestricted, including export and import of its conditions.

All checking conditions imply W. Truth is W; negation subtracts a condition from
W; conjunction and disjunction preserve the mask. A raw difference of two masked
conditions therefore tests convergence within W. No generalized cofactor or
approximate condition is used. True-throughout-W alternatives preserve logical
short circuits in the presence of exhausted operands. Unknown/blocked atoms retain
their meaning, and inconsistent assumptions retain their separate status.

Masking uses the existing BDD/work/storage limits. Same-sized truth comparisons
are charged before inspecting condition contents; no new allowance or automatic
fallback policy is introduced. W may greatly enlarge an otherwise small condition,
so measurements must include unrelated assumption groups as well as workloads
whose forbidden input combinations cause large unrestricted conditions. Report
resource regressions explicitly; semantic equivalence is not a promise that costs
or finite-budget outcomes are identical.

The initial measurements show both effects: a knowledge-form ring that exhausted
unrestricted checking now proves, while independent copies under 512 unrelated
exactly-one input groups exceed the default condition-storage allowance after
masking. Eager masking is therefore not a general storage reduction. This is why
masking ships opt-in. Changing the option invalidates checking query
identity only; shared preparation, W and admission remain eligible for reuse. A
strategy for avoiding this inflation needs separate review; increasing limits is not a fix
for carrying the same unrelated constraints in every condition.

## Certification search

Emptiness and coverage can encounter atoms blocked by an unsupported component.
Their search replays a permitted world and may attempt whole-program observation
certification. After processing a world, it excludes all worlds agreeing on the
inputs of the target's structural dependency cone **and every initially blocked
component's cone**. Coverage uses all candidate tuples of the group. Certification
only prunes rules, so later rounds cannot introduce dependencies outside these cones.
An unrelated blocked component can prevent certification; its inputs cannot be
omitted simply because they do not affect the target tuple directly.

This avoids enumerating unrelated inputs for an input-independent blocked cycle.
It does not prove that cycle or change certification's whole-program requirement.
Uncertified worlds remain unresolved. The remaining search condition stays inside
the selected W, including correlations with inputs outside the dependency set.

Dependencies reuse the existing cone analysis, are computed lazily under the
obligation's allowance, and are local to this check. Failure to finish computing
them is explicit inconclusive; a partial set is never used. Diagnostic cone
annotations retain their separate optional allowance. No limits are raised and the
uniqueness path's two-candidate certification policy is unchanged. Search can still
be exponential in the retained dependencies; failure-specific narrowing is deferred.

## Detailed condition observations

`check-den --profile-memory FILE --profile-conditions` additionally observes
retained symbolic conditions of at least 64 nodes at completed component
boundaries, failed Boolean operations and their operand sizes, assumption-build
checkpoints, and the actual input order before assumption construction. The
callback reports generic atoms; workload-specific classification belongs to the
benchmark generator. This opt-in stream neither evaluates extra BDDs nor changes
accounting, verdicts, limits or input-order selection. It adds reporting overhead
and can affect deadline-limited runs. The benchmark guide documents snapshot
semantics and bounded report aggregation. No new positive-program limit policy
is selected by this instrumentation.

## Declared input-domain evaluation

Input at-most-one/exactly-one declarations define U before selected W. Default
symbolic evaluation masks by the declared groups touching each component's closed
structural input support; semantic queries still intersect exact W. This is not
the experimental full-W checking policy: selected assumptions are not copied into
component conditions. Mask and group construction consume existing work/BDD storage
allowances. Both input cardinality kinds group the eligible tuples over resolved
domains, without enumerating absent Cartesian grouping combinations. New groups use
the existing atom bound and enumeration is charged; exhaustion is explicit. Coverage
obligations and named assumptions retain their separate Cartesian grouping semantics.
No limits or input-order default changed.

SAT input-group encoding (also used by the CNF measurement tool) uses pairwise
exclusions for at most five candidates and a one-way sequential counter above
that size. The counter reuses the first literal, omits the unused last register,
and emits n-2 auxiliaries and 3n-5 binary clauses. Five is the clause-count tie,
with no auxiliaries on the pairwise path. Exactly-one adds one coverage clause.
Existing variable, clause, literal and work limits charge the actual encoding;
this changes its size, not permitted worlds. All query-local clauses retain
their selector. Other Boolean encodings still use equivalence where needed.

Structural ordering keeps declared groups contiguous, including on heuristic
fallback; selected input exclusivity remains a weighted preference. See
[diagnostic input ordering](#diagnostic-input-ordering) for scope and accounting.


Detailed profiling also emits `recursive-component-shape` and
`recursive-component` records. A recursive component reports its atom/rule counts,
top 20 relations by atom count, and up to three closed cycles of at most 12 edges
from a bounded graph search (4,096 dependency visits and 4,096 search steps).
Truncation is explicit; no sampled cycle does not mean no cycle.

During evaluation, snapshots are sampled at most once per second, with a clock
check every 256 rule visits; completion, exhaustion and interruption force a
snapshot before approximations are cleared. They include completed rounds, current
and previous-round distinct changed heads, rule visits/evaluations, restarts,
scheduling reservation, the ten largest current conditions and the top 20 relations
by counted nodes with omitted counts. These are recursive approximations, separate
from the exact `retained-condition` observations at component boundaries.
`accountedNodes` covers the evaluator including context and reservations;
`componentNodes` sums the current component's conditions. `retainedArrays`,
`retainedArrayNodes` and `retainedNodeBytes` deduplicate shared array references,
not equivalent functions or nodes in independently allocated arrays. `resultArrays`
and `resultNodes` count newly wrapped results since the component started; they
are cumulative traffic, not live allocation or peak memory. Superseded unreferenced
arrays are dropped normally; there is no permanent BDD node store to clear here.
Profiling adds scans and output, not semantic work charges or BDD operations, and
can affect deadlines. Disabled profiling collects none of these snapshots.

## Whole-program CNF size experiment

`just measure-den-cnf` measures original residual completion and declared input
cardinality without global input-dependent BDDs. It does not select a new checking backend
or alter admission. Optional non-growing CNF elimination is limited to acyclic,
single-reader definitions; recursive boundaries and input variables stay queryable.
The report separates final CNF vector storage from reconstruction storage and makes
no peak-memory or solver-performance claim. Selected assumptions and semantic
queries follow in a later increment; the current measurements cover U only.


Optional `--simplify` compares acyclic structural hashing, U-only constant folding,
dead-body/premise elimination and syntactic subsumption, independently and composed.
Local proofs have their own cone, cumulative BDD allocation and work caps (64 atoms,
4,096 nodes, 50,000 work by default), also charging work to the variant's global
allowance. Subsumption shares 50,000 work per head. Cone cuts introduce free variables;
cardinality groups are included whole or weakened away, never truncated. Failed or
cut-off proofs leave the candidate unchanged. Cancellation/deadlines and global
exhaustion abort measurement. These are experimental measurement allowances, not
new checker policies. Each variant starts from the same original program; retained
model/mapping/rewrite vectors and CNF reconstruction are reported separately.

The original residual SCC report is independent of simplification. The optional
paired-local-proof scan uses the existing local limits and one additional global
measurement allowance. It holds the snapshot fixed while changing the local limits;
this diagnoses resource effects without tuning the policy.

## Experimental stable-query allowances

`stable_query::Engine` is an opt-in Rust API over original rules, U and a selected
verification, outside the ordinary BDD checker. Preparation and each query have
separate work/deadline allowances. Emitted CNF variables, clauses and literals use
`max_atoms`, `max_rules` and `max_dependencies`; these counts accumulate across the
engine, including selectors, exclusions and refinements. A partial clause-emission
failure makes later queries inconclusive until the engine is rebuilt.

Each query defaults to 64 refinements, 128 solves and 100,000 cooperative solver
polls. Conflict and propagation allowances default to 100,000 and 1,000,000. Batsat
exposes counters but no public setters for its internal search budgets, so these
last two caps are checked after each solve, before accepting the answer. They may
overshoot within a solve; cancellation, deadline and the poll allowance interrupt
search cooperatively. Learnt-clause storage is not included in emitted CNF counts.
No solver counter or chosen model is a golden.

Exact conclusive answers are cached FIFO, at most 32 entries and 8 MiB of owned
query/model payload by default. Setting either allowance to zero disables retention.
The prepared program is shared by models and the engine, not charged again per cache
entry. Inconclusive answers are never cached. Cache insertion is optional and cannot
turn an obtained answer into a work-limit failure; cancellation still propagates.
These allowances are provisional for the new experimental API, not changes to the
existing diagnostic probe or BDD checking defaults.

The experimental `Engine::check` gives each selected emptiness obligation and each
meaning phase its own work/deadline allowance. Individual SAT queries retain the
solve/refinement/poll/conflict/propagation caps above; they share their phase's
remaining work and time. Emitted CNF limits still accumulate across the engine.
Existence defaults to at most 1,024 examined worlds (sufficient cover cubes may
cover many more); emptiness counts at most 10,000 distinct tuples per obligation.
Exhaustion is explicit and keeps previously confirmed failures and lower bounds.
These are caller-configurable `CheckOptions`, not ordinary checker defaults.

`CheckOptions::meaning` defaults to `Full`; `Uniqueness` skips existence and `None`
skips both. Explicitly skipped phases remain not analysed even on stratified programs,
and keep the aggregate incomplete. Property checking and attribution still run.

Existence enumeration appends each sufficient input cube once under a dedicated
selector. Enumeration searches retain the ordinary per-query caps and shared phase
budget, but bypass ordinary answer-cache lookup and insertion. Other queries retain
their exact-key cache. All emitted clauses, including old enumeration selectors and
full-observation program queries, accumulate under the existing engine CNF limits.
No cross-check solver compaction is introduced. Existence searches use compact
original dependency cones for negative components with determined upstream. Each
has independent completion/refinement and enumeration gates; ambiguity in an upstream
cone triggers whole-program fallback. Eligibility queries validate two cone models
against the same W. Cube certification, eligibility, all cones and fallback share the
existence work/deadline/world allowance, including the initial stratification scan;
there is no new allowance per component. A certificate that exhausts is never used.
All scoped encodings accumulate in the engine's existing CNF allowance. Compact cone
vectors are released between components; their emitted clauses remain gated.

Existence statistics count produced cubes and their widths, the whole-program encoded
input support, distinct inputs touched, emitted exclusion payload and selector
literals. `distinctCubeLiterals` counts a literal once per distinct cube, not once
globally. The union of touched input indices is bounded by the encoded input universe;
accounting uses the phase work budget. Aggregate counts sum work across scopes,
including repeated upstream coverage and fallback; a cube is distinct within its own
scope. `scopes` reports each component's support and counters, eligibility/result state
and one-based processing position. `componentsTotal` counts original negative
components; `fallbackReason` explains any whole-program search. Component ordinals
are local to the prepared residual graph, not reusable semantic identities.
Numeric progress snapshots use the existing
250 ms throttle, forcing the initial sample and scope completion/exhaustion. Final
statistics are also retained in the report; instrumentation does not choose cubes.

Uniqueness has its own single phase allowance. Completed local cone proofs can discharge
it without another pair query; otherwise a downstream/upstream-closed scope excludes
unrelated work. Scope construction, pair search, full-model extensions and any
whole-program fallback all use the remaining uniqueness work/deadline allowance and
ordinary per-query caps. Skipped or unfinished existence proofs never narrow the scope.
The callback deadline cap is restored after each query, including fallback, so it cannot
shorten a later check. No limits or input-order policy changed. `uniquenessStats` records
the scope and attempted pair/extension queries separately from existence counters.

The diagnostic sample uses the existing emptiness policy: three examples in semantic
key order by default, or a caller-selected bound/all examples. Each example's
derivation and dependency-input annotation have separate fresh diagnostic allowances;
they are collected after semantic checking and cannot affect completeness. Answer
inspection is charged before a violation query so materialising a confirmed failure
cannot erase it through work exhaustion. Retained models share their prepared graph;
each retained world still costs a bitvector over the program. Whole-check reports
are not cached, and the lazy uniqueness encoding can roughly double program CNF.


The stable-query CLI is selected with `--engine sat`; it has no session cache or
editor setting. `at_most_one` groups share their obligation's work/deadline allowance,
with the existing per-query SAT caps. A linear prefix encoding asks for at least two
true tuples; it does not allocate a quadratic set of pair queries. Group enumeration
and fixed coverage enumeration remain bounded. Fixed relations are classified once
from residual membership, independent of selected assumptions. All fixed obligations
are evaluated directly, including coverage/exactly-one; symbolic coverage and notices
remain deferred. Optional uniqueness attribution uses separate per-tuple allowances.
This is a corpus-validation mode, not a feature-parity or performance claim.


### Stable expression oracle allowances

Each `constant`, `equivalent` or `synthesize` call shares one checker work/deadline
allowance across its primitive queries. `OracleLimits` defaults to 256 queries,
128 split branches, 1,024 expression nodes and 64 distinct available values.
These are per-call bounds, configurable through the Rust API. Cached queries still
count toward the query allowance. Each primitive search keeps the existing
solve/refinement/poll/conflict/propagation caps, while emitted CNF totals continue
to accumulate across the engine. A partially emitted expression query poisons the
engine just like a partially emitted ordinary query; rebuild before reuse.

Synthesis tries constants first, then a bounded iterative Shannon search in the
caller's available-value order. Shared nodes and equal branches reduce the result;
this is not cost-based synthesis or a minimality guarantee. Infeasible branches are
don't-cares only within the stated stable-model context. Exhaustion returns
inconclusive, not non-expressibility or a proof. A non-expressibility answer requires
two validated interpretations that agree on every available value and disagree on
the target. Models, exact subquery answers and valid loop refinements use the existing
verification-local retention rules. Supplied-expression mismatch queries are not
separately memoized; no unsat-core generalization is enabled. No corpus performance
claim or ordinary BDD/default-limit change accompanies this API increment.

### Plain execution-plan construction

The experimental `denotate-plan` driver leaves checker defaults unchanged. It uses
stable meaning of the original requested-output cone. The same scoped engine owns
meaning, branch feasibility, extraction and support reduction. Preparation waits
until outputs are supplied; changing the output set prepares a fresh engine rather
than retaining multiple scopes. Full grounding/evidence remain retained. Preparation
and meaning/oracle operations keep their existing limits. Scope construction and
output expansion are charged, with no new allowance or performance claim.
Preparation keeps its own checker deadlines and is excluded from the driver's
construction clock. Driver graph/expression work
has its own `max_work` allowance and elapsed deadline, checked before publishing a
plan and between oracle calls; one call can overshoot that deadline up to its own
cooperative bound. Cancellation propagates as cancellation. Default plan bounds are
100,000 operations and 256 oracle calls, with the existing per-call expression
bounds. Split defaults are depth 16 (hard ceiling 64), 128 attempts and 256
candidate guard/component pairs per ranking step; support reduction gets 64 trials
per build. Candidate retention is bounded before insertion. Ranking prefers balanced
edge removal, then total removal, then semantic keys. Only the best candidate is
tried; no backtracking. Both arms consume the shared construction allowances;
optional support reduction also consumes oracle calls. Reported plan size counts
implicit joins separately from the operation cap. These are foundation limits,
not corpus-tuned policies. No partial plan is published on exhaustion. The reference interpreter also requires an explicit work allowance.

Ready-work scans and grounding are retained in this increment. The driver does not
yet implement lifted plans, a partition shared with meaning/checking, incremental
plan caches, or a corpus-scale performance claim. Each child specializes its output
cone; sibling joins share a continuation, but unrelated branch states are not merged.
See [the plan README](../crates/plan/README.md).


SAT subsumed-producer notices run under an independent diagnostic allowance. Their settlement
support walk must exclude the entire source rule being reported, so a proof cannot
justify deleting its own support. Exhaustion is exposed as `subsumptionIncomplete`
and never alters semantic completeness or exit status. Presentation shows at most
eight distinct head tuples and sixteen supporting locations per source notice,
with omitted counts. Full affected instances remain in the checker report. No
corpus-scale timing or memory claim accompanies this propagation increment.

Syntactic subsumption is part of the independently charged settlement preparation.
It compares same-head signed body sets after propagation, shortest first, with
semantic-key tie breaking. An aggregate cap of 100,000 pair comparisons bounds the
optional optimization: unvisited producers survive, with no claim of exhaustive
redundancy reporting. Heads lacking semantic ordering keys are also left intact
(for the existing partially keyed query API). Indexing, keys and comparisons also consume preparation work;
ordinary preparation exhaustion remains explicit. No SAT/BDD query is involved.

The SAT CLI's component inventory gets its own 1,000,000-work, two-second allowance,
independent of meaning limits. Each sample retains at most twelve cycle edges and
reports the exact omitted edge count. A search cutoff marks the inventory incomplete;
completed components remain visible. `--dump-component` reuses the existing bounded
JSONL writer for SAT's prepared graph, including full component atoms and surviving
rules with original identities. These reporting bounds never alter verdicts.

### Obligation-scoped SAT meaning

Opt-in `--sat-meaning cone` uses the same limits, reduct checks and decomposed
existence search as full SAT checking, inside the selected obligations' upstream
union. Fallback searches that union only. W and its full input universe stay
independent. Uniqueness is omitted; universal properties do not need it. Exhaustion
remains explicit and cannot become scoped success. Scope construction and graph
rebuilding are charged to preparation; there is no new allowance or default change.
The scope does not reduce full grounding or retained evidence memory, and residual
atom slots are preserved. No performance improvement is promised by this increment.

### SAT input pins and one-level meaning partitions

Optional W-only pin discovery tries at most 256 named inputs, prioritizing negative
cones, with work bounded by the supplied checker max_work unless a smaller optional cap
is configured.
Each query retains the existing SAT solve/refinement/poll/conflict/propagation caps.
Unknown discovery leaves inputs unfixed. Work has a `SatInputPins` receipt, including
optional cutoffs; it is not a verdict. Propagation of proved pins and final encoding
are charged to preparation. Cancellation/deadline cannot publish a partial engine.

Automatic split ranking considers at most 8 exactly-one input groups of at most 32
members, with ranking work bounded by checker max_work unless a smaller optional
cap is configured. Ranking does no SAT
search and retains only complete candidate scores. A cutoff without a completed
candidate falls back to ordinary unsplit meaning. Hints restrict selection, not
semantics. Inputs/derived values outside the selected partition are not assumed.

Branch feasibility queries share the outer meaning budget. Each nonempty branch has
its own preparation and ordinary per-phase work/world/CNF allowances and existing
per-query SAT caps; work can therefore multiply by the bounded number of members.
All branches share the outer remaining deadline. This explicit first-increment
policy avoids unbounded/nested partitioning; it is provisional until measured on
real programs. No runtime or memory improvement is promised from synthetic tests.
Unknown arms keep meaning inconclusive unless that phase already has a confirmed
failure. Properties and the separate diagnostic allowances are unchanged. The CLI
exposes pin/ranking caps and a relation hint, including zero-candidate disable controls.


### Task scheduling foundation

Task descriptors use the planner's existing node/work/depth/oracle allowances.
Additional scope dependencies are charged to checker preparation; no new SAT truth
semantics or default changes accompany them. Changed task metadata invalidates scope
preparation. Task splits retain the remaining continuation inside both arms, trading
larger plan structure for simple one-shot execution without task-state merging.
Interpreter bookkeeping is bounded; a host callback itself is not preempted by its
operation counter. This increment makes no corpus-scale performance claim.

### Optional completion size analysis

The positive-support LFP used only for completion size diagnostics is opt-in
(`--completion-size-lfp`), independent of verbose/JSON/profile size output. It has an independent
work/atom allowance and a cooperative deadline of the configured timeout or five
seconds, whichever is shorter, per grounding attempt. Raising the production timeout
does not lengthen this optional pass. Its time, including cleanup, is excluded from
semantic preparation; its cutoff leaves circular-only counts unknown and does not
change a verdict. It reports progress and cutoffs. Its semi-naive propagation runs
seed rules once and recursive readers only for new tuples, retaining join indexes
across rounds. GFP observation counts are recorded once per relation; examples
inspect at most 1,024 tuples, so exact counts need not have an example. All its joins
use concrete tables; unbound sort-domain enumeration stops the diagnostic comparison. This does not alter
the completion GFP semantics or its limits. CLI preparation counts are flushed
before checking searches, including partial counts when preparation stops.

### Completion encoding reductions

Before CNF allocation, completion performs an incremental Fitting propagation within
the frozen query scope, under unrestricted inputs. It preserves unseeded positive
self-support and does not use H or W to settle atoms. Work is charged to the existing
query allowance; there is no new limit or default-budget increase. Gate-local literal
normalization, body deduplication, conjunction sharing and direct single-definition
clauses reduce private Boolean registers. Named atoms remain protected query and
replay targets; the measurement experiment's general named-variable elimination
requires a separate reconstruction contract before reuse here.

Input-only restrictions add formulas over the existing world variables. General
assumption cones and paired interpretations retain independent copies. Rejection
reuses classification equations across its two solves with the appropriate H pin;
its exclusions never constrain the H-existence query. Per-copy allocation details
are measurements, not policy goldens. The transient GFP peak is the demand checked
against `max_atoms`, not cumulative work, final ground size, or a memory peak.

### Anchored completion descent

Completion's positive-support greatest fixpoint now uses provider-first SCCs and
anchored coordinate updates within them. A relation is anchored only if each producer
can bind all variables from concrete positive tables or has an empty premise/domain.
Process every pending anchored update before an unanchored finite-domain fallback;
install smaller tables immediately and reschedule readers. Monotone descent from top
preserves the same greatest fixpoint, including unseeded cycles. The original atom,
work and deadline allowances still bound it; no policy budget is raised.

The transient atom allowance counts fixed preceding components plus concrete current
component tables, replacing the coordinate being evaluated. It excludes the old copy
of that coordinate while constructing its replacement, so it is not a live-memory
cap. Work records per attempt include scope indexing/traversal and grounding stages,
including partial attempts. The optional LFP comparison is excluded from that work.
Provider dependency indexing is lazy and shared within preparation; no-provider runs
pay no indexing cost. Detailed records let corpus runs distinguish scope discovery,
GFP descent, rule instances and graph analysis before changing any limits.

### Completion preparation common work

Validate and normalize finite domains once per preparation, including constants in
all authored rules, and reuse the result for provider, provisional and runtime
grounding. Build the original advisory dependency templates and head index once;
provider engines and the runtime engine share that immutable value. This removes
repeated whole-program scans without changing live scopes, provider determinacy,
meaning or any allowance. Preparation is fresh on every invocation.

With size reporting enabled, `preparationWork` accounts for every successful charge
of the preparation budget, by orchestration stage and by the charge's phase. It also
reports rejected work charges separately and survives early returns before any
grounding attempt. Stages distinguish common setup, provider scope/grounding/query
work, provisional grounding, runtime grounding/setup, assumptions and classification.
The per-attempt records are a breakdown of this total, not additional work. The
optional diagnostic LFP and later checking searches use independent budgets and are
excluded. Counters describe logical work, not timings or memory, and are not goldens.


### SAT CLI exploration policy (2026-11-22)

`check-den --engine sat` and `plan-den` use a shared cooperative 120-second deadline
across preparation and subsequent queries. It starts after loading and covers all
selected verifications (or the selected plan). `--timeout-ms` overrides it; creating
a new query, replay budget or planner phase does not restart it. SAT callbacks use
the remaining time. Loading, rendering and uninterruptible allocations are outside
hard preemption; this is an exploration time box, not a real-time guarantee.
BDD/editor defaults and the Rust API's default limits are unchanged.

Structural CLI guards remain 5M atoms/CNF variables, 7M rules/CNF clauses and
50M dependencies. Automatic search guards scale with the configured time box
(rounded up to whole seconds): per second, 1B work, 100k solves/refinements,
100M polls, 1B conflicts and 10B propagations. These are generous runaway guards,
not throughput estimates. World/cube and tuple inspection caps remain 100k and
5M. Explicit flags override each corresponding cap, regardless of argument order.

Completion partitioning retains the whole run's automatic guard as a floor for
each child, including setup. This deliberately avoids dividing a large program's
fixed folding/encoding cost by its branch count. The absolute deadline and fair
child time reservations still bind; no time is added. Explicit logical caps keep
conservative division and can still exhaust early. `Limits::search_guards` carries
this opt-in operational policy; it is absent from default library/editor limits.
Structural/CNF/output guards remain separate and can stop a runaway early.

Re-scoring evidence: a real program's runtime-grounding sample (at cde4fd1) spent most time in
joins, phase-accounting maps and the optional diagnostic LFP. The new selective-join
control has 3,000 left and right tuples and 6,000 connecting tuples; it completes
under the unchanged Rust API defaults with either authored premise order. Runtime
work is reported in the local handoff, not asserted as a golden. The private corpus
must be re-run to establish its next bottleneck; this is a provisional CLI policy.

### Completion join indexes and observation cost

Completion tables index by bound columns with hash maps. A probe hashes the bound
values and visits only its matching bucket; indexes are built once per column shape
per table and updated for diagnostic LFP appends. Hash iteration never chooses
bindings: tuple buckets retain deterministic row order. Each join step chooses the
smallest matching concrete bucket under the current binding, with deterministic
premise-order ties. The diagnostic delta still seeds semi-naive joins. Negative
premises and finite-domain fallback keep their existing semantics.

Preparation accounting interns static phase addresses into counter slots, with a
small fixed cache; hot charges update integer counters, not string-keyed trees.
Textual phase totals are assembled at publication. These addresses are private to
one run and never become identities or serialized data. Join work/calls accumulate
per authored rule and orchestration stage; reporting keeps the top 32, ties by
semantic key. Index-build work belongs to the first rule that requests that index.
The observer retains a counter per visited rule/stage until preparation ends.

Stage elapsed times exclude the separately bounded diagnostic LFP, but the shared
run deadline includes it. Each completion search reports elapsed time and scoped
work (unavailable if construction failed before the query runner existed). Nested
search scopes can overlap; do not sum them. Neither times nor counters are goldens.
Anchored-first descent is unchanged: a shrunk provider can reschedule its readers,
which still rejoin from scratch. The sparse-cycle regression records those calls;
no descent-delta cache is introduced without evidence that it is the next bottleneck.


### Completion descent measurements

The `guarded-schema` [zoo family](../scripts/SHAPE-ZOO.md#guarded-schema-completion)
separates fact-row growth from depth at fixed block counts. Its impossible-root
control forces shrinking propagation; it is reported separately from the ordinary
forest. Measure preparation stage work/time and completed atom/rule counts, with
identical source and limits on both builds. Partial attempts remain visible and
are excluded from completed-stage fits. No growth slope is a correctness golden.

Descent uses removed-tuple joins and affected-head rechecks with the existing work,
atom and deadline limits. Pending heads are subsets of retained possibility tables;
it does not cache a second set of ground rule instances. This is not a guarantee
of linear joins: projection onto a shared head can require rechecking many
alternative supports, and symbolic-to-concrete changes can still require a full
join. The opt-in diagnostic LFP continues to use its own growing delta frontier.

### Completion existence and evidence at scale

Existence first proves totality of negative components over free boundary providers;
positive components need no SAT totality search. A component that is not total is
retained with its upstream cone for the global search. Before existence encoding
and cube construction, retain the reduced view's cyclic SCCs (positive as well
as negative), H, restriction targets, and their upstream closure. The omitted
acyclic equations have a unique topological extension for each retained model and
input observation. Reconstruct that extension before original-equation replay;
semantic classification membership does not shrink. Existing total-component
certificates still justify the earlier residual reduction.

Model cubes fix only the retained interpretation, allowing the acyclic remainder
to vary with unpinned inputs. SAT lifting attempts up to 64 deterministic block
deletions against those retained equations. Each lift encodes the check for its
model's derived values (constants fold away) under its own gate. Every solve
assumes each inactive gate false, so over thousands of cover rounds solves carry
thousands of dead gate assumptions (a first real program's leaf slowed to 3.7
rounds a second before hitting the 50M-literal budget after 8,813 rounds). The
opt-in `completion_retire_lift_gates` (`--completion-retire-lift-gates`) retires
each gate when its lift ends: a unit clause keeps its clauses off and the gate
leaves the assumption list. The clauses stay stored and counted (batsat 0.6 does
not remove satisfied original clauses), so retirement bounds solve assumptions,
not CNF size. It also changes the solver's search path: on the formula control the
property search no longer reached an obligation counterexample the default finds,
so it stays opt-in until a corpus A/B decides. Encoding the check once, with
derived values as assumptions on fresh variables, was measured and rejected:
thousands of assumptions per solve made rounds three times slower.

Cover telemetry is per cover loop (each loop's selector; at most 16 loops retained,
a new loop releasing the oldest loop's record and pin counts): cubes, pins, inputs
pinned in every cube (a count and a sample of 8, each with how many cubes pinned it
true), the 8 most-pinned inputs among the rest (with their true counts), the 8 inputs
pinned with both values most often (by the smaller of their true and false counts,
always-pinned inputs included: a toggle pinned both ways is being enumerated), and a
coverage estimate: per declared at-most-one or exactly-one input group, read as the
split ranking reads them (a derived field-value group maps to its inputs when each
member's live producer has one unknown premise, a positive input), the share of
values a cube still allows, 1/2 per other pin, summed over cubes. It assumes those
groups and all other inputs are independent, ignoring other W correlations and
branch conditioning, so it is neither an upper nor a lower bound; projected cubes
are cubes / estimate. The group index is built only when sizes are measured, once
per preparation (it reads only the declared input groups and the assumptions), on
its own budget: 256M work and a quarter of the question's remaining time, the same
cancellation and run deadline, so telemetry never spends the question's work. Past
either cap the estimate is reported unavailable; a time cutoff is not shared, so
later searches try again. `groupIndexWork` reports the build's work on the search
that built it. `liftedPins` can
exceed `liftingAttempts`: one attempt can drop a block of pins. Forcing records name
up to 32 forced witness atoms with their constants.
A progress signal for deciding between
covering and splitting, never evidence. H-coverage, its no-H fallback, and the
ordinary residual existence query use the same boundary for CNF and cubes, and all
three lift their cubes: the no-H fallback lifts against the no-H encoding (on a first
real program, one leaf whose inputs mostly had no H model ran 94,940 unlifted
rounds). Rejection also lifts its H-model cubes, keeping the H pin when H is an
input. W and
formula-pin constraints retain their independent encoding and context. Pair
(uniqueness) queries use the same boundary with the compared decision atoms as
additional roots: both copies encode only the retained equations, every compared
difference lies on a retained atom, and each reported pair is reconstructed and
replayed in full. Without declared decisions every derived atom is compared, so
nothing is omitted. Semantic scopes and obligations are unchanged.
The [presence repro](../fixtures/completion-lifting-scope/README.md) compares the
old fixed-model cubes with this extension certificate and a source-level rewrite,
including set-valued endpoints where a scalar restriction would be incorrect.
All work, solves and deadlines remain charged; the lifting cap never changes a
verdict, and exhausted required searches remain inconclusive. Component validation
uses compact arrays. Global validation indexes retain every original producer and
constant while skipping unrelated producer-less false slots.

With a shared run deadline, required searches get an equal share of the remaining
time by remaining question count (each obligation counts once). Rejection precedes
ambiguity; classification existence, a diagnostic, runs last on the share it would
have had beside the gating questions; accepted-input eligibility remains
independently checked. Unused time passes forward. Preparation, input-contract
validation, global cancellation and the final deadline are unchanged. No time or
count is a test golden.

Search size records include `existence`: component totals/fallbacks, rounds, cubes,
sum and maximum pins per cube, model-validation work and lifting attempts/removals.
Counts are operational and may be partial; a local fallback is not a finding.
Progress exposes the same running counters. Default completion evidence retains
64 atoms per model and 64 present/absent inputs each, with omissions explicit;
retained examples still follow the existing example limit. Full models require
`--completion-full-models`. Shared model references are local to one report.

### Reusing completion eligibility and obligation searches

Eligibility lifting uses deterministic block deletion within the same 64 SAT trials
per model: attempt the entire cube, then split blocks whose removal fails. Two
independently validated models, H and their differing decisions remain valid on
the intersection of the lifted cubes. Required search limits charge every trial.
Processing candidates discarded by eligibility need no full processing replay.
Successful eligibility restores a candidate at the same observation before replay.

Eligibility pairs and property witnesses validate once in full, then maintain
original-rule truth and producer counts as variable values change. The index and
previous values are private to one immutable cone/encoding. Work charges include
index construction, reading variable values and affected-rule/head validation;
`validationWork` continues to report actual charged validation work. Input
restrictions are checked on every model. A failed update aborts that query.

One solver encodes W and the property cone per obligation, with incremental tuple
or group assumptions. Eligibility exclusions can be reused because they describe
ambiguous classification independently of a property target. One validated model
may witness multiple present tuples, but never a universal absence claim. SAT
solve/poll/conflict/propagation windows remain per part as before reuse. Work and
deadlines remain shared by the obligation; CNF limits now bound the retained solver,
including definitions accumulated for groups. No limits or CLI defaults increase.

### Completion odd-cycle cores and bounded failure triage

Component totality first uses linear signed-SCC/parity analysis. Parity-consistent
components require no SAT boundary enumeration. The remaining search retains
odd-cycle SCCs and their upstream providers. Guarding cubes can prove totality
without freezing derived assignments; the existing model cube is retained when
smaller. These are sufficient proofs; failing parity is not evidence of no meaning.
No search limits increase. Work for graph analysis, cubes and validation is charged.

Completion size records include each search's `workByPhase`, whose entries sum to
its cumulative `work`, including on cutoff. A work exhaustion's subphase is the
operation that could not obtain another charge, not the cost of that operation.
The optional counters intern static phase identities and use a small integer cache;
there is no string-keyed tree lookup on every work unit. Size records and progress
also name the current component, its atoms/rules/boundary, bounded relation list,
and parity-inconsistent SCC count. `oddComponents` counts SCCs, not all cycles.
Completed records retain at most 64 components and 32 relations each, with omissions;
the current component remains visible even after that record bound.

Odd-cycle explanation is advisory work with a separate allowance: at most
1,000,000 work and 100 ms per explained component, further restricted by the
configured limits. It pauses the enclosing local time allowance and does not
consume its work; global deadlines and cancellation still apply. No semantic
result is inferred from explanation exhaustion. It is skipped without progress
or size recording. Signed parity analysis still precedes optional explanation.

The search retains up to three conflicting-edge seeds per signed SCC, visits
one seed from each SCC before second seeds, and stops after finding three distinct
simple odd cycles in the reported component. Rotation deduplicates cycles.
A cycle longer than 128 edges is omitted whole, with an omitted count. Each edge
shows at most eight alternative producers and sixteen other conjuncts per
producer; omissions are explicit. Negative-edge histograms count rule-instance
occurrences by consumer/provider relation; guard-input histograms count distinct
graph edges per input group. The latter traverse original producer dependencies
structurally, including derived guard tests. They do not assert that changing any
one input disables an edge. Both histograms retain at most 32 rows by descending
count, with deterministic tie breaking and omitted-row counts. A cutoff labels
partial counts; the distinct-cycle count is always a lower bound, even after all
selected seeds have been searched. This policy does not alter pruning or splits.

Completion failure triage stops at `max_failures` distinct failed parts per obligation
(default eight in the API). The CLI derives that bound from `--empty-examples`
(default three; `all` disables early triage stopping). This changes enumeration,
not a confirmed verdict. A truncated count is explicitly a lower bound. Ordinary
solver/time limits still apply, and a real cutoff remains inconclusive. Resource
measurements and selected examples remain observations, never goldens.

### Completion SAT allowances

Each completion question owns one cumulative allowance of solves, solver polls,
conflicts and propagations (`--sat-max-solves`, `--sat-max-polls`,
`--sat-max-conflicts`, `--sat-max-propagations`). Every solve the question issues
debits it: repeated solves on one solver, temporary local-uniqueness solvers,
certification runs, ranking trials, probes, branch units and resumed deferred
leaves. Replacing, nesting or resuming a solver never refreshes it. Narrower caps
(a unit's share, a trial's or probe's cap, each run's own `config`) form a chain
below the question's: a solve debits every level once and may use only the
smallest remaining balance, so ordinary-mode floors for units stay clamped by what
the question has left. Standalone passes (observations, world queries, assumption
analysis, advisories, planning queries, provider preparation, pruning passes) own
one allowance per call across their runs. Obligation parts keep their per-part
reset of the run's allowance.

`used > limit` exhausts a resource, so a zero conflict limit still allows a
conflict-free solve. A solve is refused before it starts when no solve remains or
an earlier call already overshot; during a solve, conflicts, propagations and polls
interrupt it at the solver's next checkpoint (batsat checks between decisions, so a
run of consecutive conflicts can overshoot by a few; cooperative, not an exact cap).
An interrupted solve is inconclusive, naming the resource; a solve that proves SAT
or UNSAT at the crossing checkpoint keeps its answer. Cancellation and deadlines
take precedence over allowances, and an unsplit probe's work cap is reported as
work. The checker uses batsat 0.6.0 with one added setter for its internal budgets
(`third_party/batsat/PATCHES.md`); the stable path's limits are unchanged.

### Completion component determinacy

Uniqueness first probes relevant cyclic components with shared, unconstrained
boundary values. Acyclic regions and certified local functions share literals when
their boundaries are shared. Non-unique components use reachable pair searches;
remaining coupled choices require the joint residual pair described in decisions.
This reduces duplicate CNF, but a large recursive component may still exhaust its
query allowance. It does not introduce planner splits or raise limits.

Local probe CNFs are released; their work, solves, polls, conflicts and propagations
are cumulative within the ambiguity query. Fallback encodings remain gated in the
query's retained solver and count against its physical CNF limits. No proof or
encoding is retained across invocations. Size/progress records distinguish
`local-uniqueness`, `reachable-decisions` and `coupled-decisions`; states include
`searching`, `solving`, `unique`, `fallback`, `ambiguous` and `incomplete`.
`fallback` is not an ambiguity finding. Local sizes describe the temporary solver;
reachable/coupled sizes describe the retained solver, including inactive clauses.
`uniqueComponents` counts local proofs and `sharedAtoms` counts the resulting shared
boundary closure, including inputs and fixed/out-of-scope slots; it is not a count
of saved SAT variables. Solver sizes are emitted before solving, with elapsed time after
the component query; reporting bounds remain 64 records and 32 relation names.

### Completion producer pruning

This experiment is opt-in: `CheckOptions::prune` / `--completion-prune`, default off.
The 275-format double-giving regression became slower with pruning and lost a
previously conclusive ambiguity result to a deadline. Default checks retain the
unpruned path. The semantic oracles continue exercising pruning explicitly.

When enabled, before encoding a checking question, try coverage and producer subsumption with
the target head's equation disabled and the other scope equations unchanged.
Candidates are unsettled heads in odd components or cyclic components independently
shown non-unique with a free boundary. Locally unique and acyclic heads are skipped.
The existing parity-witness BFS and negative-edge relation histogram rank candidates;
processing first retries heads successfully simplified under classification W,
re-proving each candidate in processing. This scheduling set includes every successful
head, independently of capped diagnostic records; H-only successes are excluded.
Among other heads, multiple-producer heads precede unary heads. Heads receive
round-robin turns within these priority tiers: first
coverage, then individual subsumption candidates. A subsumption candidate must cut
an internal edge not supplied by another remaining producer. Successful changes
update subsequent proofs. After a changed round, targets and ranking are rebuilt
from the proved prefix, and earlier failed candidates are retried. This narrows
advisory warnings as well as proof work;
semantic scopes and equations outside the proven transformations remain unchanged.
Fitting substitutions for proof setup are computed with all candidate definitions
abstracted, so they cannot smuggle the disabled equation into a proof.

Each round has an incremental proof solver; all rounds share one view budget.
Optional pruning reserves at most one third of the invocation timeout, divided
equally across selected verifications, then classification (when present), processing,
and property work (when present), then W/W+H. W cannot spend H's reservation;
property scopes share one bucket. When a classification or processing view saturates,
its unused reservation is divided equally among buckets not yet started in that
verification. Unfinished views and cutoffs release nothing; started views receive
no retroactive extension. A single property view cannot release the shared property
reservation. Separate verifications retain their independent reservations. The CLI
sets `Limits::pruning_allowance` once per verification; standalone API checks use
one third of their invocation timeout. A reservation is additionally capped at
one third of the time remaining when checking starts, preserving search time
when preparation was expensive. Classification and processing views are
built before semantic searches, independently of splitting. There is no five-second
view cap or extra quarter-query cap. The absolute run deadline still applies.

Target discovery gets one quarter of the view's remaining time/work, at most
500 ms. Each candidate solve gets a fair slice among active heads (denominator
capped at 16), at most 250 ms. A candidate-only deadline advances to the next
candidate. A changed round retries candidates using refreshed targets. Stop
reasons are `saturated` (a complete unchanged round without unresolved attempts),
`candidate-cutoff` (an unchanged round with unresolved proof/discovery attempts),
and `overall-cutoff` (the view's cumulative work/time/query budget stops it).
A completed candidate queue alone is not saturation. Proven prefixes survive all
optional cutoffs. These allocations are provisional.
Work is reported separately under `completion pruning W` or `completion pruning W+H`.
Proof work is not charged again to the semantic search's work allowance. An optional proof cutoff is reported
in `simplifications.cutoffs`, not as semantic incompleteness; the subsequent search
can still finish. Global deadline/cancellation behavior is unchanged.

H views extend the same frozen scope's W-pruned view. Classification parity/shape,
H-model coverage and the no-H fallback all use the corresponding pruned view;
returned models still validate against original equations.

Views are retained only during that check invocation. Reports keep 64 component
summaries (16 ranked candidate examples each), including considered/proved counts,
last head and optional cutoff. Human output prints cutoffs without `--verbose`.
Reports keep 64 proof records
and 32 source instances per record, with omitted counts; conditional branch
records have a separate 64-record allowance so root findings cannot crowd them out.
These caps do not limit
installed proofs. Source findings group by head/context and bound primary source
contributions to 32. Repeated scopes may count the same instance more than once;
counts describe transformations of solver views, not distinct authored rules.

This is provisional candidate ordering, not a promise that pruning is cheaper than
the query it precedes. Equation gates and proof pins still scale with scope size.
Measure the guarded-schema `--schema-double 1` profile/splice shape before changing
limits or adding path splitting.

The optional disjoint-downstream determinacy shortcut inspects all original equations,
including hidden constraining equations. It skips the coupled fallback only if every
candidate component's downstream closure is disjoint. To keep this add-on cheap,
it declines scopes with more than 100,000 atoms plus rules plus body occurrences,
or insufficient remaining work for its charged traversal. Declining leaves the
existing coupled query in place; this is not a corpus-scale optimization yet.

### Completion input partitions

Input splitting is opt-in: `CheckOptions::split_depth` /
`--completion-split-depth`, default zero. `split_branches` /
`--completion-split-branches` defaults to 512 terminal partitions per question.
Only partitions whose separate values plus rest fit the remaining cap qualify;
a binary input split may still fit when a group partition does not. Reaching a
depth or leaf bound uses the existing residual search. No input choices are
silently dropped.

Ranking uses one compact parity witness per odd component, or a directed cycle
in each decision-relevant component independently shown non-unique. Guard-input
reachability stops at every cyclic atom, including positive/even cycles. The top
64 partitions form a bounded inventory, alternating inputs and formulas in their
own witness-involvement order (structural score breaks ties). Up to eight are trialled: each kind has four slots
when both have enough distinct groups, with unused slots available to the other.
Distinct groups precede alternate subsets. Trials share one quarter of remaining
setup time/work; each candidate receives a share of the remaining allowance, and
failed/discarded trials are charged back. Before trials, the parent views are
reduced once; children share their incidence indices and propagate changed pins.
Trials are ordered by the number of witness cycles their guards involve. Equal
shares have a provisional 500 ms floor: reduce the number of trials to fit that
floor and stop starting trials when it cannot be met. Unused shares pass on;
there is no new allowance. A partial trial with verified cuts remains eligible
and ranks by its observed cuts, without credit for unchecked children. Those
children still receive residual checking. With no verified cut, use the unsplit
query.

Verified ranking first prefers the sum of per-child witness cuts / extra children,
then cycles cut in every child, then total disabled edges / extra children,
minimum disabled edges, structural rank and stable order. At least one child must
cut a witness; a one-sided cut is eligible. Per-child `cyclesCut` exposes which
side progresses; the common-cut count is no longer the primary score. An edge remains live if any producer
still supplies it. A cut is a graph observation, not proof of existence/uniqueness.
The bounded inventory distinguishes untried, verified, and incomplete trials;
additional certified groups can report no acyclic guard or a partition-cap exclusion.
The best verified alternative is reported beside the winner.
Input at-most-one groups include an absent case. Selected derived
cardinality groups qualify only through injective one-positive-input equations
in their own assumption cones. A second live producer disqualifies that shortcut;
otherwise binary input splitting remains available.

Only values distinguished by the targeted component get separate children. Rest
pins those distinguished values false, leaving all other values unknown; it stays
available for deeper splits. Reaching a bound falls back to residual search.
Closing one component is never taken as a proof for another; parity proves
existence, while local uniqueness needs a pair query.

Root Fitting builds producer/reader indexes once per scope. Child states use
copy-on-write pages and propagate changes from the new pins; they share program
tables and indexes. Dense fixed-value materialization, graph/ranking passes and
residual encodings still cost work per visited child. Local uniqueness for ranking
is charged and its query use is subtracted before children or residual searches.

For ordinary processing-existence and ambiguity searches, an enabled question
prepares its ancestor views and ranks partitions. If none cuts a witness cycle in any child, run the question once with
all remaining time/allowance. An inconclusive result does not trigger a duplicate
unsplit search. If a verified partition exists, reserve half for one unsplit attempt;
only an inconclusive answer starts partitioning from the already prepared/ranked
root. Conclusive results return immediately. Ranking is bounded to a quarter of
the question's time/work; an optional ranking cutoff leaves residual search.
Classification existence instead enters the structural driver before its cover,
within its bounded question share. Exploration uses the probe-first policy below.

Traversal is deterministic and breadth-first. Every child ranks its residual
components; components untouched by the selected split are not excluded. For a
component cut in some children, ordinary processing/ambiguity sends its unchanged
side to residual checking rather than recursively exploring that same target.
Classification existence and exploration re-rank all surviving targets. Other components can still
select a split on that path; after new pins, components are rediscovered. Child
ranking has a bounded quarter of its unit's remaining setup allowance, with
residual checking after optional ranking cutoffs. Cutting one witness never proves another component safe.
Explicit work/solver/round allowances are divided evenly among children, discarding
integer remainders. Automatic CLI guards retain the run-wide floor described above.
Pending units share the remaining question deadline. Each unit, including nested
SAT calls, inherits the earlier of the outer deadline and its own remaining-time
share; descendants cannot consume the time reserved for queued siblings. A cutoff in any child prevents
a universal
success; a confirmed counterexample can still be returned from another.
Branch reports retain 256 records per invocation and 32 input pins per record,
with omitted counts. Report caps never cap search completeness.

This is provisional. Dense query setup and repeated local uniqueness discovery
can cost more than splitting saves. Children inherit both context-tagged ancestor
views and propagate pins in each: W+H for H-first coverage/processing under H,
W for no-H fallback/rejection. Ranking uses W+H when available; this never turns
an H-only result into a no-H result. New branch-relative proofs run only in ranking
trials (024.32); selected children inherit the winning trial's proved views and do
not start an additional pruning pass merely because they were selected.
Measure the identical guarded-schema `--schema-typecut 1` workload with
splits off/on before changing defaults. Cross-unit caching and parallelism remain
future work.

The initial 275-format type-cut measurement (depth 2, default limits) did not
improve checking: 84.6 s unsplit versus 99.8 s split, both incomplete. Four
questions each partitioned into 275 leaves; all children exhausted their shares.
Processing existence was conclusive only in the unsplit run; the same three
obligation failures remained confirmed. This is evidence for keeping depth zero,
not for increasing budgets. Reusing or narrowing branch preparation should precede
any claim that wide partitions help the corpus.

Value-slice follow-up (2026-11-23), same-build profiling runs of the same
275-format shape and its `--schema-fieldcut 1` variant, at default limits:

| Shape | Splits off | Depth 2 | Partition result |
| --- | ---: | ---: | --- |
| Declared type group | 85.16 s | 92.15 s | 12 binary-sized group splits, 16 leaves |
| Derived field-value group | 48.23 s | 82.94 s | 12 binary-sized group splits, 16 leaves |

Both split runs closed four leaves and left twelve inconclusive. Processing
existence stayed conclusive, and the obligation counterexample remained in all
four runs. The field-value run found classification ambiguity with splits off,
but exhausted its divided allowances with splits on. These partitions avoid the
earlier fan-out; they do not yet demonstrate a throughput or completeness gain.
Keeping splitting opt-in is still warranted. These are single-run observations,
not regression thresholds; the local handoff records commands and setup costs.

Ranking/unsplit-first follow-up (2026-11-23), same 275-format field-value shape,
default limits, same profiling build off/on: 44.91 s / 57.44 s. Classification
existence now chooses `observed_value(type_field, tag_0)` first (7 distinct affected
edges, 2 children), with another type value as the tied runner-up; rest later
chooses `tag_1`. The first unsplit classification-ambiguity attempt confirms its
counterexample in 5.34 s, so this question is not partitioned. Both modes retain
the same confirmed outcomes and inconclusive questions. The split mode visits
8 leaves (3 proved, 5 inconclusive) after 6 splits. This meets the selection and
witness-preservation regression, without demonstrating a speedup. The half-share
policy remains provisional; a harder witness can still need more than that share.

Completion solvers retain an absolute deadline in addition to their local timer.
Nested solvers inherit it; branch questions use the earlier of the run deadline
and their allocated question deadline. An elapsed shared deadline takes precedence
over solver-poll exhaustion in the reported cause. Completion solve intervals
are reported separately from enclosing query elapsed time; they do not include
nested solves twice. The deadline remains cooperative: a solver operation between
callbacks, output or destruction can finish after it. A late observation is recorded
as an overrun, not treated as a conclusive answer.
CLI progress also separates preparation, checking, engine cleanup, result output
and size output, and reports the point at which the shared run deadline starts.


Verified-cut follow-up (2026-11-23), pruning enabled in both modes, the same
275-format fieldcut shape: 73.93 s off / 78.69 s depth two, equal outcomes and
incomplete overall. Classification-existence selects type-field values and cuts
its witness in every child; ambiguity still needs partial cuts and residual search.
The certified catch-all control (`--schema-decoycut 1`) takes 93.71 / 85.13 s;
all three hard questions select the type field at root, never the catch-all.
Splitting confirms a classification ambiguity that off leaves inconclusive;
classification no-meaning and processing ambiguity remain inconclusive. These
single runs are not a speed claim. Peak RSS rises from 2.69 to 2.85 GiB for fieldcut
and 2.76 to 2.95 GiB for the decoy, including inherited views and branch setup.
W+H now receives nonzero proof time independently of W; time-limited proven
prefixes and optional optimization notices can differ between modes.

Pruning-round/split-hygiene follow-up (2026-11-23): the same-build 275-format
fieldcut control, pruning enabled and default time-box policy, took 104.4 s with
splits off and 106.5 s at depth 2. W+H removals were comparable (873 / 870), rather
than disappearing in split mode. Classification ambiguity and three property
failures remained confirmed in both; processing existence was proved, while
classification existence and processing uniqueness remained inconclusive on
deadlines. Split mode used three split decisions and five residual leaves.
All six pruning views reached their overall time allowance in round 1: this is
not evidence of saturation. Small oracle tests cover completed pruning rounds.
There is no speed improvement claim; the private corpus still needs re-scoring.


### Completion pruning under branch assignments

Enabled only by combining pruning and input splitting. Root pruning keeps its
full reservations and redistribution policy regardless of split mode. Trials are
funded from the existing split-ranking allowance (at most a quarter of the
question); each ranking pass credits its available trial time fairly to W and
W+H, without replenishing explicit work/query counters. Candidates and children
share these counters. Setup, unsuccessful queries and discarded candidates are
charged too. An individual attempt uses at most half the caller's remaining
time/work, leaving room to propagate and rank its proved prefix.

Saturated root views first redistribute unused time to unstarted root buckets.
Only a remainder with no such recipient can supplement ranking, transferred once
and reported as `trialReleasedMs`. Property reservations stay with their other
property cones. A transfer can at most double the normal ranking time, leaving
at least half the question for unsplit/residual search; unused credit remains
available to later questions. Extra time stays inside the original deadline;
the overall run deadline and explicit limits still bind. No root reservation is
reduced to fund trials, and no fresh allowance is created per candidate or child.

Discovery follows alternative producers for at most 32 witness heads, inspecting
at most 32 producers and retaining 32 guard atoms per head. Upstream traversal
still stops at cyclic atoms. The existing eight-candidate trial shortlist is used.
For each child, try one common-equations pass on those witness heads under W and
W+H separately, then rank actual edge cuts in the resulting Fitting view. This
is bounded proof search, not a pruning fixed-point claim. Keep candidate child
views only for the best two trials with verified cuts; discarded views are released. The
selected trial's views are reused without proving them again. Uncut children and
children whose targeted cycle closes still receive the full residual question.

Conditional findings retain up to 32 assignments per proof with an omitted count;
cache identity always uses the complete assignment set. Grouped findings display
at most eight distinct branch conditions. Discarded trials publish no source
findings. Trial telemetry counts all work independently of these presentation caps.

Derived guards with wholly acyclic upstream in the current branch view also
enter the candidate pool as two-child formula partitions. Inspect at most 64
derived guards in edge-score/key order, within the existing ranking allowance;
input and formula candidates share the 64-entry inventory and eight-candidate
trial shortlist. A compact input-formula DAG travels with each derived pin and is
asserted in every branch search; independent local/assumption certificate queries
remain unrestricted. The DAG is independently evaluated on returned input models.
A direct complementary pair is skipped as a useless constant partition; this does
not install a forced atom. No other forcing or cyclic cutset splitting is added.

Formula certificates retain original scope and W/W+H. Mixed H-first/no-H
classification existence currently admits W-valid formulas only; questions wholly
under H may use the stronger view. H-only formula branches do not attempt W
pruning. Parent formulas remain constraints in descendants, so later formulas may
use their settled values. Root pruning shares, unsplit-first policy and residual
checking are unchanged.

After selection, sample surviving witness guards in every child, with 32 guards
shared across the split. Each child receives a share of the remaining slots;
unused slots pass forward. Record omissions and completeness per child (with zero
slots, an inventory may consist entirely of omissions). The diagnostic pass shares
at most 1/16 of remaining ranking work/time and 50 ms, divided among the remaining
children as well. Diagnostic cutoffs cannot discard the selected partition.
Per-trial child records separately report pruning attempts/proofs, removed producers
and literals, at most eight pruned heads, target-atom settlement and witness cuts.
To identify removed self-admitting producers, each child also keeps up to eight
original ground bodies with up to 16 literals each, their proof context and omitted
counts. These source examples are distinct from the shared 32-guard inventory.
Settlement is a count for the targeted components, not a verdict for the child.

Before restoring root shares, on the 275-format guarded-schema field-value control
(`self=50`, `double=1`,
`wide=1`, `depth=2`, `fanout=5`, `stmts=3`, `triggers=1`, `fieldcut=1`), two
default-limit profiling runs with pruning and depth-2 splits finished in about
107.5 s. Both retained the emptiness counterexample and proved processing
existence, but classification ambiguity became inconclusive where the saved
prior run confirmed a counterexample. Classification existence and processing
uniqueness remained inconclusive. Trials took about 4.2 s and proved 53–57
simplifications, none retained by a selected partition. Root pruning used about
32.6 s, with all six views cut off in round 1. Reserving trial time reduced root
classification-W successes from 284 to 281; the contribution of that reduction
versus changed query costs has not been isolated. This is evidence of an
allocation trade-off, not a scale improvement. This motivated restoring root
shares and funding trials from ranking instead.

With root shares restored, the same default-limit control recovered confirmed
classification ambiguity and matched the prior run's other verdicts in 107.35 s.
Root pruning used 39.03 s (about 6.49 s allocated per view); trials used 3.90 s,
212 attempts / 47 proofs, again with none retained by a selected partition.
No leftover root time was transferred. This establishes recovery on the public
control, not a scale benefit from branch pruning. The private corpus remains to
be re-scored.

### Implied positive body literals in completion views

With `--completion-prune`, targeted odd/non-unique heads also offer positive
in-component body literals for SAT-proved removal. Search-free one-atom supports
now run on all live rules before target discovery (see below). For other
implications, share the existing gated common-equations encoding with
coverage and producer subsumption; try literal implications after that head's
coverage attempt and before its producer-removal attempts. Updated bodies receive
new equation gates, while original scopes and validation stay unchanged.

The SAT path uses existing pruning work, time, query and candidate-slice allowances;
there is no new limit. Branch trials use the same
mechanism and retain their context/assignment boundaries. Telemetry counts
`removedBodyLiterals` separately at record, component, view and aggregate levels;
proof records remain bounded and omitted counts explicit. No corpus performance
improvement is inferred from the lowerer's equivalent rewrite.


### Search-free reductions precede completion graph analysis

Fitting and indexed positive-body implications run on all solver views before
components, odd-cycle explanations and ranking. They use the checking caller's
existing work/deadline allowance. Initial reduction precedes optional root pruning;
reductions between proof rounds also count against the enclosing pass's elapsed
time. After a SAT rewrite changes equations, reduce the changed prefix before the
next analysis; unchanged cached views do not need another pass. Child propagation keeps
its persistent indexes; analysis materialization performs the reduction separately
and tentative ranking pays for it from its existing allowance.

Inactive rule slots remain for source identity and original-model validation.
Semantic scopes remain fixed by live GFP. This does not introduce stable-model
unfounded-set reasoning into completion. On reduction exhaustion, keep the supplied
view and its already-proved prefix; no spent budget is restored. Private corpus
component-size improvements require a new run, not inference from small controls.

### Completion SAT shadow caches

A fixed-query family owns its immutable CNF and its W/H context exclusively.
Models are indexed by per-variable bit columns; cores use one watched literal,
a signature prefilter and exact subset checking. Core insertion skips a core
subsumed by an existing one. The first implementation retains at most 4,096
models and 16,384 cores, with separate 8 MiB storage allowances; full caches skip
insertion rather than evicting or changing a solver answer. There is no global
cache or reuse between encodings, contexts, workers or invocations yet.

Shadow lookups always run the actual SAT query and compare the claimed result.
Telemetry distinguishes model/core claims, checked claims, mismatches and skipped
insertions. A resource cutoff can leave a claim unchecked; it cannot validate the
claim. Model reads are disabled while removable clauses are active; this slice
also declines all core writes in that case, rather than trying to retain selector
conditions. Batsat's conflict literals are negated back into assumption literals
before subset indexing.

Forcing enforces **model** hits by default (`Limits::completion_cache_enforce`;
`--completion-cache-shadow` restores shadow mode). This is Boolean-only and
forcing-only: forcing reads just SAT/UNSAT, and an enforced hit does not update the
solver's model, so a caller needing a witness must solve. A wrong SAT claim can only
leave an atom unforced; constants come only from UNSAT answers, which the model cache
never gives. Every 100th claimed model hit, starting with the first, is re-solved:
a conclusive contradiction is a hard internal error, while a re-solve interrupted by
an allowance reports its cutoff and is not a disagreement. A hit costs lookup work
only (no solve, conflicts, propagations or polls); the sampled re-solve spends the
ordinary allowance; cancellation and deadlines are checked on hit paths. Core hits
stay advisory; core enforcement and cover-loop integration are later work.

### Optional per-path completion forcing

`--completion-force` / `CheckOptions::force` defaults off and requires positive
split depth. In ordinary mode it runs in funded child trials and branch units.
Processing existence and ambiguity retain their initial unsplit attempt;
classification existence reaches covers only after the structural driver. Within the existing
ranking allocation, forcing receives half the available time/work/query allowance,
shared across applicable W and W+H views. Unused work passes on; explicit logical
limits and the run deadline still bind. This does not reserve time from root
pruning. Trial ranking counts forced witness atoms before the existing verified
cut scores, while requiring at least one actual cut to select a partition.

Each pass builds one immutable encoding, checks context satisfiability, and then
queries positive/negative literals as assumptions. No-model contexts install no
constants. Every installed constant has a residual defining-equation constraint,
unless the forced view already implies it: a retained definition blocks the
structural existence certificate (no odd component and no retained equation), so
after each forcing pass installs its constants (or finds none), one SAT query in a
fresh solver, under W, the branch pins and H for W+H, asks whether the view without
any of its retained definitions (installed here or inherited from an ancestor
branch or the W pass) has a model violating one. If not, the constants alone define
the same models and the definitions are dropped (`discharged` in the forcing
record). A SAT answer keeps them; a cutoff keeps them and the installed constants
and is recorded as the pass's cutoff. Without this a constant could remove a node's only odd component
(ranking then finds no split target) while its retained definition sent the node
into a cover loop enumerating inputs the constant made irrelevant. Iteration with
propagation and pruning stops at a fixed point or cutoff. Queries,
failed work, shadow-cache work and installation are charged. Cutoffs leave the
last successfully installed equivalent view. No node, time or selected-witness
golden is introduced; compare outcomes and inspect per-path telemetry.

### Opt-in completion exploration scheduling

`--completion-explore` (`Limits::completion_exploration`, default false) removes
implicit time/work/SAT-query subdivision from completion pruning, discovery,
ranking, child trials, forcing, siblings and search questions. The 500 ms trial
floor and per-candidate pruning timeout do not apply in this mode. All shortlisted
trials are attempted in deterministic order unless an explicit resource limit or
the invocation deadline stops them. Existing candidate/output caps remain.

Mechanism switches are independent. Exploration schedules classification existence
last, after the gating questions, obligations and optional advisories. Its verdict
and aggregate effect are unchanged. Default mode retains a bounded question share
and reports the active component, cover progress and cutoff resource.

With splits enabled, each exploration unit first gets a deterministic unsplit
probe: `--completion-probe-work N`, provisionally 256,000,000 work units including
SAT callback polls (0 disables it). On the first real program the cheap questions
needed 17M-83.5M; a hard question's probe at 1,000,000,000 took about 7 s. The
default leaves about three times the largest measured need; it is not a timing
target. A conclusive probe bypasses
forcing/ranking. The probe runs the ordinary unsplit search, including existence,
rejection and eligibility covers and lifting, under that cap; it reuses existing
views and never starts pruning, forcing or ranking. Exhausting the cap is charged,
is never a proof, and leaves the remaining allowance to the structural driver; a
counterexample found inside the probe is reported as one. This does not promise
that every ordinary unsplit proof fits the cap. In exploration, every unit that finishes
its structural work without a split, the last structural unit included, is recorded
as `leaf-deferred`; residual searches run only after every pending unit has been
ranked and split, so one unbounded leaf search cannot starve sibling units. Leaves
then run smallest first, by unfixed atoms in cyclic components of the question's
applicable view (W+H when it ranks under H, W otherwise), ties in queue order; a
heuristic, since a small residual need not finish quickly.

Split ranking trials candidates in shortlist order (witness involvement first) and
stops at the first trial whose children, the rest child included, are all verified
and each cut a witness cycle; that trial is selected. A trial that cuts only some
children is kept as the fallback while ranking widens down the shortlist within the
same allowance. Untried candidates are reported `not-started`. Residual checking is
unchanged. `Limits::completion_full_shortlist` (`--completion-full-shortlist`)
trials every shortlisted candidate, for comparisons. A unit whose ranking finds no
partition records why (`rankingGap`: the witness cycle used and where candidate
discovery stopped). Exploration trial children prune but do not force; the selected
partition's children force in their own units, so a cut that appears only after forcing
cannot win a trial (on the first real program forcing found no constants in any trial).
A view already pruned to a fixed point is not pruned again until it changes (forced
constants, a successful proof, new pins). A cutoff proceeds to reductions, requested pruning to
saturation, forcing, complete shortlisted trials, then a verified split. Residual
queries run only at leaves. Both cut and uncut children rank surviving components.
Ordinary mode changes only classification existence's order: enabled forcing/splits
precede its covers. Processing existence and ambiguity keep their established first
attempt, and rejection/acceptance keep their direct unsplit searches. The
256,000,000-work probe and the new rejection/acceptance driver are exploration-only. Incomplete trials never justify omitted
children or proofs. W/H boundaries, residual constraints, validation and confirmed
finding aggregation are unchanged.

The CLI's whole-run timeout still starts after loading and covers preparation and
all selected verifications (120 s unless explicitly changed). Every mechanism
honors that deadline and cancellation. Automatic CLI work/solve/poll/conflict/
propagation runaway guards use a fixed 10^12 rather than a timeout-derived value;
explicit flags win. These generous exploration guards are not proposed defaults
for normal checking. Structural limits stay independent. Existing per-search,
per-view and property-part ownership remains; siblings debit actual question
usage rather than reserved fractions. Work/counter snapshots are inclusive in
nested scopes, not additive across every progress event.

Live progress shows current work and SAT polls, starts, completion, cutoffs and
not-started stages. Emission is throttled, but throttling never decides how much
work runs. A slow early phase can consume the whole invocation and leave later
questions incomplete; that is visible, not evidence that they are intrinsically
hard. Use the measurements to design deterministic production allowances later.
No timing/counter goldens or performance claim accompanies this scheduling mode.
