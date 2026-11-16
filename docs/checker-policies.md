# Checker performance policies (provisional)

These policies are in force today. Each was chosen from measurements on synthetic
and test-DSL workloads, not on real user programs, so each is **provisional**: re-score
it when real programs exist, and change it on evidence.

| Path / policy | Decision | Why |
| --- | --- | --- |
| Checker backend | BDD only; cached coarse BDD in editors | Predictable, canonical conditions; good warm reuse |
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
Groups disjoint from all other groups are contiguous blocks; overlapping groups
are preferences, and every constraint remains enforced. Eight FORCE placement
passes use integer centers and semantic-key ties, retaining the best weighted
span cost seen. No platform-dependent floating-point ordering is used.

The heuristic charges preparation work and stops at one million cumulative
structural entries or four million traversal/placement visits. These optimization
cutoffs return key order, with the reason and spent work retained in the report.
They bound expanded support and metadata, not bytes or BDD nodes. Global work
exhaustion and cancellation still propagate. CLI progress/profile records expose
`inputOrder` (requested/effective order, fallback, inputs, structural entries,
hyperedges and completed passes); non-default runs also print it on stdout.

The backend configuration includes the requested order. Shared contexts partition
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
only with raised cutoffs (the support expansion is quadratic there) and moves BDD
node counts by at most 0.5% in every phase; its guarded-bound storage comes from
the number of retained conditions, not the order. Key order stays the default and
structural order remains a diagnostic; there is no plan to change the default.

## Backend retirement

BDD is the only supported backend. The SAT experiment showed wins on synthetic and
test-DSL workloads, but no demonstrated need on real programs. Maintaining it multiplied
implementation and validation work for each obligation kind and made diagnostics depend
on a setting. Its coverage path still depended on BDD evaluation, so it could not help
when that evaluation exhausted. Its backend implementation and selectors remain retired;
Git history retains the experiment. The diagnostic probe below separately uses batsat.

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
measurements. Each negative atom's exact-producer union is built once per candidate
and released after its readers; no pruning result or guarantee cache crosses
candidates or snapshots. Candidate results retain the domain, component, snapshot,
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
extra snapshots. Symbolic evaluation and summary construction still cover the
residual program. No new allowance is introduced; `admission-candidates` profiling
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
batch boundary described above. Neither recovery applies to shared evaluation or
transactional graph installation, nor raises the storage cap. Earlier global work remains charged, so a
later unrestricted bound can still exhaust work before another guarded attempt.

Failures in shared symbolic evaluation or summaries, total work limits and other
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
has its own allowance; residual grounding, specialization and the cycle index share
an independently bounded validation allowance and `AssumptionValidation` receipt
which depends on `FixedFacts`. Request attachment and W remain charged to preparation.
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
The first implementation evaluates fresh whole-program symbolic meaning to obtain
constraint conditions, ignoring unrelated blocked components, then checks through
the whole-program path. This can exhaust on unrelated work; the result is explicit
inconclusive. Restrict evaluation to the constraint cones only when measurements
justify it and the same independent semantics is preserved.

Local verdict caching remains enabled for input-only at-most-one contexts. General
constraints invalidate the absent-extension argument for projecting W into a local
query. Their verdicts are recomputed; grounding and plan reuse remain available.
A future optimization must retain or correctly quantify every external constraint
input and preserve cold/warm results, replay, consistency and cancellation behavior.

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
