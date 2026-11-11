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
bound to one corpus, domains and limits, not cached across edits. Residual grounding,
semantic indexes and admission still run per verification; local queries may
reconstruct fixed evidence rules. Cross-edit sharing is a separate increment.

Assumption declaration validity is a program-level query. The IR classifies
relation-stratified cones and those requiring grounding; the checker resolves the
latter against its unrevised ground dependency graph, without selected assumptions.
The editor and CLI run `validate_assumption_cones_for_run` before their verification loops,
so unselected declarations and unconfigured programs still get diagnostics. Keyed
cycle evidence goes through the shared presenter; it is never reconstructed there.
Validation recomputes from each complete snapshot. Its sealed `ValidatedAssumptions`
artifact can initialize fixed preparation, so selected restrictions reuse the same
original-graph check. Only relation-to-cycle summaries and keyed cycle evidence
survive; the temporary original ground graph is released. Without that artifact,
folded API preparation computes the check lazily once, including unnamed restrictions
and later selections. Corpus, domains, keys and deterministic limits bind the reuse.
Both paths use the original ground dependencies: a fixed-false guard must
not erase a negative cycle from assumption validation. Logical exhaustion remains
explicit for requests needing the check; cancellation/deadlines are not cached.
This is run-scoped sharing, not reuse across edits or an admission cache.

Selected general assumptions are another preparation boundary: once their meaning
is independently established, the checker computes W before admission.
Input-only at-most-one contexts retain local memoized queries. General contexts use
whole-program BDD evaluation and fresh W, while retaining grounding/plan reuse:
local absent-extension and constraint-projection shortcuts are not sound for general
constraints. No context-dependent BDD or verdict is reused across selections.

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
