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
graph rebuilds remain global. Logical downstream exhaustion is separate from
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
round; they own only their domain, live/dead flags and traversal metadata. Bound
values are restricted while accumulating rather than retaining masked copies for
every producer. A successful certificate promotes only the referenced summaries
to individually shared ownership, preserving its executable snapshot after later
rewrites. Its storage remains conservatively charged after the round ends; no
borrow or ownership of the entire previous round escapes into the certificate.

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
without retaining a growing event history. Process-wide readings are observations,
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
instance; other fixed premises drop out. This is one specialization, with no repeated
folding, selected assumptions or admission proofs. Blocked fixed atoms remain unknown.
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
fold across input-dependent edits. Logical exhaustion remains inconclusive;
cancellation/deadlines never install partial reusable preparation.

Selected general assumptions are another preparation boundary: once their meaning
is independently established, the checker computes W before admission.
Input-only at-most-one contexts retain local memoized queries. General contexts use
whole-program BDD evaluation, with W shared only within the same selection:
local absent-extension and constraint-projection shortcuts are not sound for general
constraints. No context-dependent BDD or verdict is reused across selections.

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
