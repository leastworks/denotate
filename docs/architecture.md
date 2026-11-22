# Architecture

Denotate is layered so that the IR's meaning is defined once, in Rust, and every
consumer (the CLI, the `.den` editor, a DSL editor) shares it exactly.

```
                     grammars/den  (Tree-sitter grammar of .den)
                          │ compiled into
 crates/test-dsl ─lowers─► crates/ir ◄── crates/ir-text (.den load / print / index)
                          │                    │
                          ▼                    │
                 crates/normalize              │
                          │                    │
                 crates/check  ──►  crates/check-session (cached sessions)
                          │                    │
                 crates/presentation (interpret checked evidence)
                          │
                 crates/editor (LSP mechanics, scheduler, lifecycle, edits)
                          │
           crates/den-lsp (.den editor)    crates/test-dsl server (test DSL editor)
```

## Crates and their responsibilities

| Crate | Owns | Does not own |
| --- | --- | --- |
| `denotate-ir` (`crates/ir`) | Typed relational construction (`Corpus`), namespaces, occurrence identities, `Sources`/`Provenance`, semantic keys, recipe installation | Syntax, checking, wording |
| `denotate-normalize` | Boolean normalization recipes (double-negation cancellation, Lloyd–Topor with linear helpers); no dependencies | Spans, IR handles |
| `denotate-check` | Finite grounding, admissibility, concrete replay, BDD property checks, contextual condition queries, no-meaning and rewrite findings, limits and cancellation | Editors, sessions, wording |
| `denotate-plan` | Experimental plain Boolean execution plans, explicit output scope, value availability, dependency order, export and reference interpretation; consumes checker meaning/expression proofs | New truth semantics, input admission, task implementation, code generation, filesystem, editors |
| `denotate-check-session` | Reusable checker sessions: plan, grounding and verdict caches, retention, warm/cold equivalence | Scheduling, LSP |
| `denotate-presentation` | Frontend-independent interpretation of checked evidence: finding identity, kind, severity, notes, primary/related placement, labeled fallback | LSP types, DSL vocabulary, filesystem |
| `denotate-editor` | Language-independent LSP mechanics: documents, synchronization, transport, the checking scheduler and server loop, lifecycle, publication, workspace edits, LSP positions | Roots, manifests, ownership, DSL concepts |
| `denotate-ir-text` | `.den` parsing, strict loading, printing, embedded origins, folder-root membership, the incremental editor index | Workspace discovery (except the `filesystem` command adapter), buffers, scheduling |
| `denotate-analysis` | Rule linting (singleton/unsafe variables, arity and sort evidence) reused by the `.den` index | Name resolution for `.den` (lives in `ir-text`) |
| `denotate-lsp` (`crates/den-lsp`) | The `.den` editor: root catalog, home programs, snapshot bridge, editor services, checking and publication, Go to Origin, rename | Language semantics (delegated to `ir-text`) |
| `denotate-test-dsl` (`crates/test-dsl`) | Test DSL: parser, lowering, attribution, wording, export layout, its LSP server | Generic checking or presentation |

## Rules that keep the layers honest

- **One resolver.** The strict loader and the editor index share name decoding,
  visibility and lookup keys (`crates/ir-text`). The editor never re-implements
  `.den` scoping.
- **Meaning lives in the checker.** Presenters interpret checked evidence; they
  never re-derive outcomes. DSL presenters may replace wording and choose extra
  related locations, but keep identity, classification and evidence.
- **Buffers are authoritative.** Editors supply snapshots; the core performs no
  disk reads. In the `.den` editor, unsaved manifests and open DSL buffers come
  from the VS Code extension through the snapshot bridge
  ([PROTOCOL.md](../crates/den-lsp/PROTOCOL.md)); a failed lookup never falls back to disk.
- **Publication is validated.** A result is published only if the complete current
  observation (members, manifests, membership, homes, origins, configuration)
  still matches the one it was computed from.
- **Provenance is separate from identity.** Semantic keys never contain file names
  or source offsets; provenance maps occurrences to source spans per view.
  Current `.den` text and upstream DSL origins are separate tables.
- **Keep computation suitable for incremental queries.** Semantic results depend on
  explicit inputs, including logical limits, rather than hidden state or incidental
  hash iteration order. Arena handles are local to one construction; reusable semantic
  artifacts use stable keys and bind back to the current corpus. Operational deadlines
  and cancellation abort work and are not retained as semantic results. Logical
  exhaustion is reported explicitly without erasing established findings; attribution
  limits remain separate from checking completeness. Cache boundaries are chosen from
  measurements: sessions already reuse planning and optionally relation-SCC grounding,
  while coverage and emptiness verdicts are recomputed. New cached stages must
  preserve cold/warm behavior and current-snapshot provenance.

Symbolic evaluation records atom-local BDD/storage exhaustion separately from
component-wide failures. Unknown conditions and their originating atom/resource
travel with evaluated state; owned local queries project both atom identities to
semantic keys. Presentation names these supplied causes rather than tracing
dependencies again. Restarting an affected positive component prevents partial
fixed-point conditions from being published as exact results. Positive components
schedule readers of changed atoms in deterministic sparse rounds; the reverse
index is invocation-local and includes replacement dependencies. Its optional
storage reservation is released before falling back to scanning on storage
pressure. Profiling may expose partial approximations during this computation,
but they remain observations and cannot enter proof or session results.

Restricted input domains follow the same boundaries: `Corpus` validates provider
signatures and their static, stratified dependency cones; the checker evaluates them
before seeding input atoms. Complete eligible tuple sets are explicit semantic-keyed
inputs to session grounding. The `.den` frontends prepare eligibility once in the
run's fixed preparation; the ordinary preparation API does so per request. Provider
relations may also participate in fixed-fact evaluation. No partial result can
enter the grounding cache.

The `.den` CLI and editor construct a `FixedPreparation` once per checking run,
independent of assumption selection. Relation dependence follows both positive and
negative premises. Settled input-independent atoms become concrete true/false
providers; unsettled atoms remain in the residual graph for ordinary admission.
The artifact shares original fixed rules, components, dependencies and derivations
as evidence, separate from the executable residual graph. Replay and presentation
still resolve original occurrences, including completed-but-absent providers.
Retained evidence and residual sizes are reported separately. This artifact is
bound to one corpus, domains and limits. Within the run, requests with the same
selected restrictions share residual grounding, permitted worlds, semantic indexes
and completed admission. Obligation groups, notice selection, verification identity
and example policy remain request attachments; a failed attachment cannot change
another request's context.
Admission runs cycle-relevant proof targets before downstream work. Each phase
selects a dependency-closed support graph, including settled providers, without
changing the full input-variable universe or selected assumptions. Transactional
graph rebuilds remain global. Component-owned removal/discharge batches run
upstream first and commit before later components; every commit rebuilds the
schedule. Pending proof storage can be released only with its owning batch, never
with shared summaries or committed evidence. A failed batch drops its values before
restoring storage accounting; computation is not refunded. Its retry identity uses
a representative atom and the existing pre-commit reader closure, not an SCC ID.
Admission separates the provider graph used for evaluation from the smaller set
of producer summaries used by proofs. Complete target-component producer sets and
one-hop providers for implied guards determine the final symbolic readers.
Intermediate conditions are released only after their last consuming component
finishes (including all recursive restarts); replacement leaves participate in
that schedule. Released values have explicit sentinels, so an accidental later
read is an internal error. Checking retains its existing query-owned values.
Summary groups are built atomically per producer head. A failed group suppresses
all dependent component attempts, including structural splits; incomplete producer
coverage never enters a proof. Unneeded groups are released after failures, while
shared successful groups and committed evidence remain. Summary skips use the same
representative-atom and pre-commit dependency invalidation as component skips.
Guarded candidates take upstream-first component turns, preserving each component's
ranking queue between turns. These queues and their component handles live only
within one immutable snapshot; every successful commit rebuilds them. Prepared
descriptors retain their existing explicit dependency validation across snapshots.
Logical downstream exhaustion is separate from
admission exhaustion: the completed cycle result and the optional downstream
incomplete marker are reused together under identical logical limits. Presentation
reports the marker as advisory; it never relabels an unsupported region.

Completed admission includes outstanding local proof-skip records, whose identities
are bound to the same prepared graph. Reuse carries those records and their logical
receipts; presentation projects current semantic keys and origins. Invocation-local
retry tracking keeps outcome metadata only. Guarded settlement separately retains
one restricted bounds computation within a snapshot; it is not a session artifact
and is released on snapshot replacement. Retry tracking uses pre-commit edges for bounds/discharge
invalidation and for changes to settled conditions. Bound-removal attempts use
the same conservative closure: edits within blocked components can tighten bounds.
Cheap coverage/removal also compare
producer membership and settled premises across the tentative rebuild, so blocked
changes that leave their inputs unchanged need no retry. This comparison finishes
before committing the graph or invalidating attempts, even when an SCC splits.
Completed negative removal/discharge attempts share that invocation-local
invalidation. Their metadata avoids repeated proofs and otherwise-unused bounds
or coverage; it is discarded after admission and never becomes a diagnostic skip
or part of a session's retained admission result.

The early structural split pass uses the same executable expressions and rewrite
identities, with a joint certificate shared across a component's replacements.
Scored branch cones may be reused only within that immutable component attempt.
One bounded cache owns the best pair and in-flight scoring pair; recursive frames carry local
cache tokens, not owned waiting sibling graphs. Eviction preserves the choice and
rebuilds children; storage pressure retries without retention under the same work
budget. Neither cones nor tokens enter session artifacts.
Its expressions form an interned DAG shared across leaf values and replacements;
structural combination reuses equal branches and folds direct complementary terms
without comparing domain-restricted truths. Profiling may inspect the completed
batch's expression and BDD sizes under a separate bounded allowance; that work and
its results never participate in admission decisions, receipts or cached evidence.
Local-query projection/rebinding preserve that sharing across rules. Pointer keys
exist only during traversal of an immutable graph; cached identity and equality
remain structural and semantic. Cutoff scheduling is invocation-local and uses
the same conservative pre-commit reader invalidation as bound attempts.
Each leaf evaluates the original component in topological order; dead producers
and pruning reasons stay in evidence. All replacements stage and commit together.
It reuses the checker’s pruning and SCC analysis, without a second evaluator in
presentation or session code. Keyed local queries retain the union of supporting
sources, including sources dead in a branch. Finding scopes also retain certified
positive forwarding sources. Evidence collection confirms those authored facts and
orders the expanded DAG separately from rewritten execution, preserving attribution.

Guarded settlement adds executable Boolean expressions to ground rules, preserving
the authored rule and premise occurrence. They mention only globally settled atoms;
the original guard stays in the body. Certificates retain rank-ordered reasoning and
candidate-relaxed bounds separately. Graph construction, symbolic evaluation, concrete
replay, completion, observation certification and owned local queries all consume
this representation. Local cache inputs include keyed expressions and their dependency
leaves; original dependency closure still invalidates transitive edits. Replacement
commits conservatively clear invocation-local negative/failed attempts, while later
ordinary commits also detect changes through expression leaves. Presentation owns
wording and display limits, and the CLI treats the equivalence warning as advisory.
Temporary guarded cones borrow immutable producer summaries from the current
round; they own only their domain, live/dead flags, pruning reasons and traversal
metadata. Deadness propagation can cut transitive producer chains; support outside
the rebuilt cone remains separate evidence and participates in keyed local query
closure. Optional pruning failure retains the original cone. Bound
values are restricted while accumulating rather than retaining masked copies for
every producer. A successful certificate promotes only the referenced summaries
to individually shared ownership, preserving its executable snapshot after later
rewrites. Its storage remains conservatively charged after the round ends; no
borrow or ownership of the entire previous round escapes into the certificate.

Candidate preparation shares completed liveness and exact-guarantee tests under
the most recent domain within that immutable snapshot. Exact representation and
producer-set checks prevent sharing across changed domains or relaxed exact
producers. The bounded cache stores Boolean answers and source IDs, never whole
cones, propagated deadness or reachability. It yields its accounted storage on
pressure and is released with the snapshot; it is not a session artifact.

Semantic indexing shares source schemas and declaration bindings across those
contexts. `GroundKeyView` projects atom, instance, component and rewrite keys from
the current graph when needed. It reads original and committed bodies from the
graph's existing rewrite storage; there is no second keyed ground graph or
post-admission rebuild. Local cache inputs still own complete relevant schemas,
bodies and dependencies: stable membership keys alone cannot establish unchanged
meaning. Only stable keys cross snapshots; compact handles stay within the run.

Local query inputs close original dependencies through an invocation-local index
of producers and rewrite proofs by head. It borrows the committed graph, including
fixed evidence and dropped originals, and projects only reached content. The first
local query builds it; it is released after the local queries. Neither that index
nor its handles enter session values, semantic identity or receipts.

Structural rewrite certificates keep their complete shared support graph, but
ordinary presentation and internal rewrite evidence keys project only direct
justification. The full original dependency closure above still guards reuse when
transitive support changes. Presentation bounds structural details per source
warning and expands chains only on explicit request; public finding identities
and proof coverage do not change. Immutable snapshot indexes reuse coordinates
and hashes within presentation/export. `.den` scalar coordinates and LSP UTF-16
positions keep their separate conventions; neither reads a later buffer revision.

Bound-removal certificates retain component upper bounds, lower guarantees from
exact producers and the independent exact head cover. Bounds are never executable
truth values. Default evidence and internal keys use the direct head cover, while
local query dependencies include the certificate's producer summaries and original
closure. Retained-condition accounting and memory profiling include the guarantee
and body-bound conditions. Full component support is requested explicitly; public
source-rule finding identities remain unchanged.

The session's Salsa fold query retains only semantic keys: possible tuples, original
rule-instance substitutions and the chosen producer/order of each true tuple. On the
next snapshot it reconstructs the evidence with current occurrences. Its explicit
input contains fixed relation/rule schemas, resolved domains and deterministic
limits, excluding input-dependent rule bodies and source locations. This first query
covers the entire fixed cone, so an edit within it recomputes the cone; per-SCC
provider reuse remains a possible refinement. The session retains one completed
fold, replacing it when the fixed projection changes. Checker limits bound its
computation and atom/rule counts; there is no additional byte cap, and the other
cache pools keep their budgets. The accounted retained bytes are reported separately
from bound evidence sizes. Failed or interrupted fold preparation clears the query.
With retention disabled (`max_entries == 0`), preparation uses the current corpus
directly, without constructing the portable value. Original validation, eligibility
evaluation, evidence binding and residual preparation/admission still run on each
new snapshot. Local verification queries
may reconstruct fixed evidence rules.

The one-shot `check-den` command uses direct fixed preparation, sharing it across
verifications within the invocation. It does not construct a portable Salsa fold
that it would immediately bind and discard. Editors retain that fold for later
snapshots; scorecards keep both paths available for measurement.

Optional `Profile` callbacks travel with operational limits, outside deterministic
limits, semantic keys, receipts and cached results. The checker emits scoped events
and BDD storage observations without OS access or additional semantic work.
Driver-owned memory sampling lives in `check-session::profiling`; CLI/editor phase
callbacks choose when to read it. The detailed profiler streams samples and events
without retaining a growing event history. The CLI owns bounded JSONL buffering,
periodic/boundary flushes and signal-time flushing; the checker owns throttled
intermediate progress and preserves terminal counts. Process-wide readings are observations,
never cache inputs or resource-policy decisions.

Checking progress also travels through operational limits. Synchronous, owned
callbacks reach session-backed local queries without becoming query inputs or
retained results; sessions clear the callback on return. The checker reports current
targets, operations and exhaustion using existing graph metadata. Private runtimes
inherit their source-bound caller target. The `.den` adapter resolves names and
bounded cycle excerpts, while CLI/editor own delivery. Editor events retain the
normal ticket filtering. Completed CLI verification reports flush immediately;
individual tentative findings are not published.

The checker also owns structural admission reduction. A private worklist proves
truth/falsehood, dead rules and bounded unfolded subsumption against the current
justified graph. Only blocked heads are removal targets; settled regions supply
boundary truth and supporting sources. The pass then uses the ordinary transactional commit before BDD evaluation.
Structural and symbolic rewrite certificates are explicit alternatives; structural
proofs do not contain placeholder Boolean conditions. Their flat shared evidence
DAG retains only supporting rules/facts reached by actual removals. Presentation
owns wording and current locations; source-rule finding identities and instance
coverage remain shared. Original rules remain in the local query dependency closure
and replay evidence, so pruning executable edges cannot hide an edit dependency.

Assumption declaration validity is a program-level query with an explicit run selection. The IR classifies
relation-stratified cones and those requiring grounding. For the latter, the checker
prepares assumption-independent fixed truth, grounds the residual once and builds
a specialized view: a fixed-false positive or fixed-true negative premise kills its
instance; other settled premises drop out. A ground-atom worklist propagates newly
proved true or false values to a fixpoint, without selected assumptions, input-group
reasoning or admission proofs. Structural blocking is not a truth value. The same
implementation supplies the SAT engine's stratification, components, encoding and
plan view. It retains original atom indices and maps view rules to original
instances; original graphs still provide diagnostic derivations. Ordinary BDD
admission uses the original graph. Syntactic same-head subsumption then removes
producers whose signed bodies contain a surviving producer's entire body. Duplicate
bodies retain one semantic-key-ordered survivor. This is reduct-preserving even
for recursive heads and uses no assumption or implication oracle. No new
unfounded-set detection is included. Original instance mappings survive both passes.
Validation follows dependencies from each assumption relation's atoms in that view;
computing W uses the same view. A cycle disconnected from an assumption is still
subject to ordinary admission and reporting.

The CLI/editor resolve the executed requests before validation, then pass them to
`validate_selected_assumption_cones_using`. Their union selects declarations by
semantic key; a partial CLI run selects only its executed verification. Unselected
cones needing grounding get an advisory `not-selected` result, including without
verifications. They never trigger the fold factory or make the run incomplete.
Relation-stratified classification still covers all declarations. The explicit
all-declaration APIs remain for authoring tools (`check-den --validate-all-assumptions`).
The lazy factory lets the editor use its session. When any selected cone needs
grounding, residual preparation, specialization and cycle indexing still cover the
shared graph; this increment does not restrict that graph to selected cones.
Keyed cycle evidence goes through the shared presenter, never reconstructed there.
The sealed `ValidatedAssumptions` artifact shares fixed evidence, the original
residual graph, its specialized view and the relation-to-cycle index with subsequent
requests. Original instances remain intact for admission, provenance and rewrite
warnings. This replaces separate original-program grounding; it does retain two
residual views. Copies of those views share their immutable cores across requests.

Without that artifact, a request needing ground validation initializes the same
preparation lazily, including unnamed restrictions and the optional grounding-cache
entry point. Corpus, domains, keys and deterministic limits bind reuse. Validation
and the specialized view recompute each run that needs them, even when the session reuses the fixed
fold across input-dependent edits. Residual preparation, atom settlement and cycle indexing have separate receipts
and allowances. The propagated view depends on the full residual, including
input-dependent producers; it never inherits the fixed projection's narrower cache
identity. Logical exhaustion remains inconclusive; cancellation/deadlines never
install partial reusable preparation.

Selected general assumptions are another preparation boundary: once their meaning
is independently established, the checker computes W before admission. Independent
symbolic evaluation is scoped to the selected restriction relations' ground
dependency cones, retaining the full input universe and chosen variable order for
W. This evaluation scope does not narrow grounding, validation or subsequent
program-wide reports.
Input-only at-most-one contexts without cardinality declarations retain local
memoized queries. General contexts and declared input domains use
whole-program BDD evaluation, with W shared only within the same selection:
local absent-extension and constraint-projection shortcuts are not sound for general
constraints. No context-dependent BDD or verdict is reused across selections.

Verification declarations also own their rule semantics, optional hypothesis
relation and optional decision-relation set. Requests carry those options, using
semantic keys for the relation references;
CLI configuration cannot override the authored choice. The declaration interface
supports completion. The SAT CLI and separate experimental `completion_query` Rust
API implement preparation, classification, processing meaning and selected
requirements. BDD, editor, scorecard and planning consumers still refuse completion
before semantic preparation. Stable with a hypothesis or selected decisions remains unsupported. Stable preparation, fixed
folds and cached answers are not an implementation of completion. The parser and
shared reference services remain usable for such declarations.

Input cardinality declarations belong to IR relation schemas, beside input
eligibility. Preparation builds disjoint per-input groups by projecting eligible
tuples over resolved domains, before any selected assumption. No candidates means
no groups, including an empty grouping list. Their conjunction defines U;
W is U further restricted by selected assumptions. Every verification reports the
input declarations separately. Empty U is a context error, never a vacuous proof.
The symbolic evaluator uses fixed component masks from closed structural input
support, including unresolved components. Consumer masks imply provider masks;
operands are re-masked before truth shortcuts and negation. Semantic reads use
exact W. Mask construction and retention are charged, and masks are rebuilt for
changed graph snapshots. The universe and relation schemas invalidate through
ordinary explicit preparation inputs. Programs with input declarations bypass
local cached checking until it supports legal extensions of projected worlds.

Verification checking may opt in to evaluation within independently established W
(`CheckRequest::checking_within_w`, default false). Its
symbolic meaning has a distinct type from all-input meaning: stored conditions
are exactly `c ∧ W`, including inputs and fixed truth. Admission and rewrite-proof
consumers accept only the default type, exact throughout the legal input universe U. Checking negation and short circuits
use W as truth; positive fixpoints and stratified negation are computed per world,
so discarding worlds outside W cannot affect any permitted world's result.
Whole-program checking, notices and the local coverage/emptiness pass use this
mode when enabled; default checking uses only declared input-domain masks. This choice enters
checking cache identity without changing preparation, W or admission identity.
The cached local uniqueness/no-meaning path still exports/imports unrestricted
conditions; no W-restricted value crosses that cache boundary.

BDD variable order is an explicit request configuration. The default is semantic
input-key order; diagnostic reverse and bounded structural orders use the ground
graph after fixed/`within` preparation, before W. Structural analysis never asks
for symbolic meaning. The request and its assumption-specialized view share the
same chosen map and condition-universe identity; changing the map changes that
identity without changing ground instance IDs. Shared contexts partition by both
assumption selection and backend configuration. Local query inputs carry their
actual ordered input keys, projected from this map (including a global completion
context when required), and runtime reconstruction consumes that sequence.
Structural validation artifacts contain no BDDs and can still share their graphs
across order configurations. See [ordering policy](checker-policies.md#diagnostic-input-ordering).

Contextual condition notices are ordinary keyed IR declarations selected by a
verification. The checker decides reachability and variation under that context and
replays witnesses; presentation supplies advisory wording and source-use placement.
A frontend supplies a zero-arity condition and the complete enclosing-scope relation.
No layer infers a DSL's lexical structure, assumes its conclusions, or treats a
notice as a business obligation. Notice queries currently recompute in warm sessions,
with independent bounded allowances and fresh presentation from current provenance.

Opt-in SAT diagnostics belong to the checker but never to its admission decisions
or reusable query state. Component probes borrow an admission snapshot after cheap
reductions and use exact settled BDD boundary conditions, including replacements
and W, in place of upstream definitions. They run in provider-first order with
separate per-question allowances. An unresolved provider gives unknown; subsequent
snapshots can retry after ordinary admission settles it. The guarded-candidate
probe borrows the live cone and
exact settled conditions; it uses an independent aggregate budget. Its active time
and report delivery are excluded from admission's operational deadline without
resetting checker time already spent. Both clocks still honor cancellation.
Progress transports the results to CLI/schema/zoo consumers; presentation findings
and editor semantics remain unchanged. See the [probe policy](checker-policies.md#guarded-candidate-filter).

Admission component dumps use a separate borrowed observer. The checker exposes
actual attempt snapshots and the last committed graph before propagating a deadline
or cancellation error; it does not serialize, perform IO, clone entire graphs or
retain historical cones. The CLI resolves semantic identities, names and source
locations, and streams bounded JSONL. Diagnostic allowance exhaustion and write
failures stay outside checker results. Reuse emits the reused graph without fresh
attempts. See the [dump guide](../crates/ir-text/examples/check/COMPONENT-DUMP.md).

Committed-program export uses the same borrowed graph hook. The checker exposes
live residual producers, original pre-admission producers and fixed truth; `ir-text`
streams plain `.den` under independent limits, and the CLI owns atomic filesystem
publication. Selected assumption cones are duplicated from their independent
original meaning, while the executable program uses committed rewrites. Expression
DAGs keep sharing across replacements. No BDD, cached admission or source origin
is serialized. Explicit round stops are checker control, separate from optional
progress observers and from export cancellation; they return an uncached
`StoppedAfterRound` error after the whole round. Ordinary runs are unchanged.

## Programs and checking in the editor

A `.den` program is a `den.root` folder plus its referenced libraries; a file outside
every root is a standalone program ([format](den-format.md#programs-denroot)). The
editor checks every known program in the background through one serial, fair scheduler
with a warm session per program; one job checks all of a program's verifications and
publishes their findings on the program's own files
([protocol](../crates/den-lsp/PROTOCOL.md), [decisions](decisions.md#programs-and-roots)).

## Tests at each layer

- Unit and integration tests per crate (`just test-crates`).
- `.den` round trip: the test DSL regression programs are lowered, printed to
  `.den`, reloaded and checked; structure, origins and default-limit BDD outcomes
  must match (`crates/test-dsl/tests/ir_text_roundtrip.rs`).
- Editor parity: for every parser-backed regression program, both editors publish the
  same findings (`crates/den-lsp/src/publication_tests.rs`).
- LSP scenarios over real stdio (`crates/lsp-tests/`) and installed VS Code smoke tests.

The standalone CNF size experiment (`denotate-check::cnf_measurement`) prepares the
fixed fold and whole residual graph without constructing W or invoking admission.
It owns completion encoding, bounded CNF elimination and optional U-only acyclic
pre-encoding simplification with local proofs; the `measure_cnf` example
in `ir-text` owns discovery and JSON output. It encodes declared input cardinality
but no selected assumptions, retains the original rules, and produces measurements
only. It does not participate in checker/session/editor verdicts.

The experimental `denotate-check::stable_query` API separately builds queries over
one original prepared program and selected verification, with no global BDD W or
admission. It reuses the probe's completion encoder, reduct validation and loop
refinement. Assumption-only world selection is independent of full-program models:
program equations and refinements are selector-gated. Immutable-engine query caches
include mode and the complete pins/exclusions; they never cross verification or
program boundaries. Its `Engine::check` API combines whole-program existence and
uniqueness checks with selected emptiness/at-most-one and fixed obligation checks,
keeping their results separate. `CheckOptions::meaning` explicitly selects full,
uniqueness-only or no meaning analysis; skipped phases remain incomplete. An existence
enumeration owns a mutable, selector-gated exclusion set and bypasses the ordinary
query-answer cache. New cubes append once. Enumeration state never crosses checks
or engine instances; its clauses remain isolated from program/property queries and
later world queries. Existence searches isolate original dependency cones of negative
components, with local existence/uniqueness establishing upstream eligibility and a
whole-program fallback when upstream is ambiguous. Each cone has its own completion,
refinement and exclusion gates; W is shared and remains authoritative. Finite-support
cubes preserve the derived interpretation in every matching world. Scoped work shares
one existence budget; local ambiguity never becomes a global finding. Global uniqueness
reuses completed local proofs within the same invocation. Otherwise
it searches the downstream closure of uncertified negative components plus upstream,
and extends any pair through full-program reduct validation before reporting it.
An unextendable pair falls back to a full-program pair query, sharing the uniqueness
phase's remaining allowance. Unclassified components are always included; measurement
records are not proof inputs. Numeric statistics are checker-owned, with presentation/CLI
adapters responsible for JSON and human output.

`denotate-check::completion_query` is a separate experimental query API. Its grounder
joins greatest-fixpoint possible tuples, retaining unseeded recursive instances and
original occurrences. Within each positive relation component it evaluates anchored
coordinates first, installs smaller tables immediately and reschedules their readers.
A symbolic-domain fallback runs only when no anchored update is pending. The same
path grounds static providers and runtime programs; provider relation scopes use a
shared, lazily built dependency index. One validated finite-domain value and one
immutable original-dependency index serve all provider and runtime attempts within
a preparation. They are rebuilt for each invocation, with no implicit cross-run cache.
It never applies stable least-model pruning or fixed folding.
The resulting live-instance graph is the frozen scope boundary for classification,
properties and input-contract checks. Liveness is the positive-support greatest
fixpoint, independent of W, H and decisions; further solver simplification cannot
change scopes. Original dependency templates remain only for advisory identities
and dead-producer explanations. Completion encoding then applies a scope-local
Fitting fixpoint over the original equations and unrestricted inputs. It substitutes
facts and determined consequences without using W or H; original atom positions,
rules and scopes remain available for queries and model validation. Literal
normalization is shared with the CNF measurement tool. Private Boolean registers
are reduced within one gate; named query/replay targets remain protected.

Selected assumptions are interpreted separately in their live cones. Over U,
shared-input pair queries test their formula's truth determinacy; cube search tests
existence. Input-only assumptions refer directly to W's input variables. General
candidate W restrictions use separate cone copies sharing only inputs, then certify each candidate against an independent false-formula query. This prevents
other assumptions, H or downstream rules from choosing helper assignments or hiding
an invalid contract. Generalized false-model cubes exclude uncertified candidates.
Static providers are checked for tuple-set determinacy before using their eligibility.
An invalid provider blocks only dependent verifications. A conservative possibility
graph may prove an input unreachable even through dead references; that graph is
never used as a verification universe. Irrelevant bounded inputs are explicitly
omitted. Structural loading checks signatures and input independence; stable consumers
keep their additional stratification validation. Completion validation is scoped
to the selected verification, including when declarations have stable consumers too.

The separate completion planner consumes checker-owned runtime context, constant,
and explicit-output meaning queries. The checker certifies classification without
consulting processing, and checks accepted output existence/determinacy in the union
of live output cones and C(H). Plan construction emits ordinary computations and
accepted-value constants, with an explicit classification barrier before processing.
The reference interpreter performs no SAT calls. Entry inputs stay actual values;
H-conditional constants cannot replace runtime classification. Stable plan structures
are shared only for neutral compute nodes, expression export and scheduling; stable
meaning, kernels and v4 export remain separate from completion v5.

Both SAT APIs share the prepared-program projection; completion has its own
scope-local Fitting encoder. The
completion API does not share stable-model refinement, attribution or solver state.
W has independent equations and the complete input universe. Classification uses
the live hypothesis cone. If its query with H has no interpretation, a separate
existence query without H distinguishes rejection from classification no-meaning.
Determinacy compares selected decision atoms (all original relations by default).
Processing retains the cone equations and H, pins its established decisions, and
asks for whole-program existence and decision determinacy. Each SAT interpretation is validated against its
scope's original equations. Exclusions distinguish relational interpretations, not
auxiliary assignments. Queries return separate rejection, ambiguity, classification
and processing no-meaning, and inconclusive outcomes; confirmed classification survives processing
exhaustion. Each query owns its solver. Whole-verification reports use shared-input pair queries
for determinacy and counterexample-guided searches with generalized input cubes
for existence and rejection. W remains independent of H and downstream equations.
Each search has a separate allowance; candidate exclusions are gated off during
certification. Property queries combine the live property and classification
cones and H, and confirm unique classification decisions separately; helpers remain
free. This preserves failures across helper
interpretations and independent of downstream contradictions. The shared completion presenter
owns interpretation evidence, JSON summary and diagnostic wording; `ir-text` owns
source placement, and the SAT CLI owns output and exit-code precedence. All-rejected
is a distinct outcome, not an unconditional proof. Invalid or unknown input contracts
retain certified counterexamples and mark universal answers incomplete, never vacuous.
Optional circular-support and dead-producer work run afterward under separate
allowances and cannot alter required outcomes.
Edits require a new immutable preparation; no session cache or editor integration
exists yet.
Emptiness uses the shared report and presentation structures; finite derivations
are reconstructed from each example's reduct-validated original interpretation
under an independent diagnostic allowance. Remaining symbolic obligation kinds and
notices are explicitly not analysed. The CLI selects it explicitly with
`--engine sat` and uses the shared property
presenter. It remains outside `CheckRequest`, sessions and editor publication;
backend identity and status are explicit in the CLI, without changing editor caches.


Stable-query preparation can also isolate the upstream union of selected obligation
relations or explicit atom roots. It uses the existing ground dependency-cone walker
on the original graph, then filters the independently propagated executable rules.
The full W encoding is built first and shares only input variables with the scoped
program encoding. Thus restrictions outside the scope still constrain inputs, while
downstream equations cannot erase a cone model. Existence decomposition and fallback
operate inside the prepared scope. Public models and oracle queries respect the
scope boundary; caches never cross it. Full grounding and original evidence remain
retained, so this is not cone-only preparation. The explicit-root API is reusable
by planning, which requires existence and uniqueness within the explicit outputs'
upstream cone. The scoped engine also serves every planning feasibility and
equivalence query, so downstream filters cannot erase an output-cone alternative.

The SAT engine may further specialize its executable view with input literals
proved by W-only queries. W and assumption validation remain unrestricted; the same
ground propagator is reused with explicit input seeds. Every engine's immutable
identity includes its verification, scope and pins. Conditional settled values are
kept separately from assumption-independent reasons/notices. Original producers
remain available for evidence. The plan driver reads this verification-local view.

For meaning, the checker can rank exactly-one input groups by propagation on negative
cones, then check each member's pinned context in an isolated engine. Those contexts
partition W, so meaning is the conjunction of arm results. Empty arms require a
W-only proof; unknown arms cannot be skipped. One level is supported, with bounded
ranking and arm counts. Arm-local solvers, refinements and query caches never enter
the parent engine. Property queries remain on the parent; the same meaning service
supports the planner without introducing a second proof path there.

SAT uniqueness and fixed-coverage reports use the same frontend-independent property
finding helpers as BDD checking. The shared presenter owns status classification and
structured meaning evidence; `ir-text` binds source locations, and the CLI owns IO,
option compatibility and exit-code aggregation. Fixed obligations do not require a
whole-program model; their evidence scope is explicitly the fixed dependency cone.


The stable-query expression oracle is checker-owned, separate from the
execution driver. Its context is a conjunction of pins minus excluded cubes;
its available-value list is a caller-supplied runtime capability, not an additional
truth assumption. Constants, supplied equivalences and bounded synthesized Boolean
DAGs are justified against stable interpretations in the engine's prepared scope. SAT mismatch queries
use isolated selectors and the existing reduct verifier. Iterative Shannon synthesis
uses only available values for branches, sharing identical expression nodes and
checking every feasible leaf for a constant. It does not establish readiness,
whole-program totality or uniqueness. Expressions can be evaluated without access to
the checker; their reachable leaves are their runtime dependencies. Exact context
memoization remains inside the immutable verification engine; there is no
cross-session expression reuse.

The experimental `denotate-plan` driver consumes this oracle and the original
prepared graph. It owns output selection, availability, the execution partial order,
and its reference interpreter; the checker owns meaning and expression proofs.
Construction requires existence/uniqueness in the original output cone, then
constructs requested output work using expressions, pure positive fixpoint kernels and
bounded splits. Expression support comes from available values in the target's
producer cone; support reduction needs another oracle proof. A split pins an
already available guard and recomputes the residual ground components. Each
feasible child supplies the same declared bindings; their values may differ.
Sibling joins share a continuation under the parent context, without importing
child-only pins or temporaries. Branch feasibility and equivalence remain checker
queries within that same prepared cone. The scheduling partition does not yet
replace the upfront cone-meaning check. Planner configuration retains immutable
program/domains; preparation waits until build supplies outputs. Equal semantic
root sets reuse the latest engine; changed roots discard it and all its query
state before preparing a replacement. Full grounding/evidence remain retained.
Plans carry semantic keys and defining-rule provenance; the `.den` export adapter
adds source and embedded origin descriptors. Interpretation requires independently
validated permitted inputs. No filesystem, editor state or DSL concepts enter the
driver. Rust task descriptors additionally identify produced inputs, applicability,
arguments and source keys. The checker only follows their supplied scope edges;
the driver schedules one-shot calls and the host implements the pure callbacks.
Produced inputs are unavailable at entry even when W pins their truth. Task branches
retain their continuation in each arm, avoiding producer-state loss at sibling joins.
The interpreter's guarantee is conditional on a permitted completed observation;
there is no runtime task-contract validator. See [the plan API and limits](../crates/plan/README.md).
