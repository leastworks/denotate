# Architecture

Denotate is layered so that the IR's meaning is defined once, in Rust, and every
consumer (the CLI, the `.den` editor, a DSL editor) shares it exactly.

```
                     den/grammar  (Tree-sitter grammar of .den)
                          │ compiled into
 test-dsl ──lowers to──►  native/ir ◄── native/ir-text (.den load / print / index)
 (InputMapping)           │                    │
                          ▼                    │
                 native/normalize              │
                          │                    │
                 native/check  ──►  native/check-session (cached sessions)
                          │                    │
                 native/presentation (interpret checked evidence)
                          │
                 native/editor (LSP mechanics, scheduler, lifecycle, edits)
                          │
           den/lsp/server (.den editor)    test-dsl server (InputMapping editor)
```

## Crates and their responsibilities

| Crate | Owns | Does not own |
| --- | --- | --- |
| `denotate-ir` (`native/ir`) | Typed relational construction (`Corpus`), namespaces, occurrence identities, `Sources`/`Provenance`, semantic keys, recipe installation | Syntax, checking, wording |
| `denotate-normalize` | Boolean normalization recipes (double-negation cancellation, Lloyd–Topor with linear helpers); no dependencies | Spans, IR handles |
| `denotate-check` | Finite grounding, admissibility, concrete replay, BDD/SAT property checks, no-meaning and rewrite findings, limits and cancellation | Editors, sessions, wording |
| `denotate-check-session` | Reusable checker sessions: plan, grounding and verdict caches, retention, warm/cold equivalence | Scheduling, LSP |
| `denotate-presentation` | Frontend-independent interpretation of checked evidence: finding identity, kind, severity, notes, primary/related placement, labeled fallback | LSP types, DSL vocabulary, filesystem |
| `denotate-editor` | Language-independent LSP mechanics: documents, synchronization, transport, the checking scheduler and server loop, lifecycle, publication, workspace edits, LSP positions | Roots, manifests, ownership, DSL concepts |
| `denotate-ir-text` | `.den` parsing, strict loading, printing, embedded origins, folder-root membership, the incremental editor index | Workspace discovery (except the `filesystem` command adapter), buffers, scheduling |
| `denotate-analysis` | Rule linting (singleton/unsafe variables, arity and sort evidence) reused by the `.den` index | Name resolution for `.den` (lives in `ir-text`) |
| `denotate-lsp` (`den/lsp/server`) | The `.den` editor: root catalog, home programs, snapshot bridge, editor services, checking and publication, Go to Origin, rename | Language semantics (delegated to `ir-text`) |
| `denotate-test-dsl` (`test-dsl`) | InputMapping: parser, lowering, attribution, wording, export layout, its LSP server | Generic checking or presentation |

## Rules that keep the layers honest

- **One resolver.** The strict loader and the editor index share name decoding,
  visibility and lookup keys (`native/ir-text`). The editor never re-implements
  `.den` scoping.
- **Meaning lives in the checker.** Presenters interpret checked evidence; they
  never re-derive outcomes. DSL presenters may replace wording and choose extra
  related locations, but keep identity, classification and evidence.
- **Buffers are authoritative.** Editors supply snapshots; the core performs no
  disk reads. In the `.den` editor, unsaved manifests and open DSL buffers come
  from the VS Code extension through the snapshot bridge
  ([PROTOCOL.md](../den/lsp/PROTOCOL.md)); a failed lookup never falls back to disk.
- **Publication is validated.** A result is published only if the complete current
  observation (members, manifests, membership, homes, origins, configuration)
  still matches the one it was computed from.
- **Provenance is separate from identity.** Semantic keys never contain file names
  or source offsets; provenance maps occurrences to source spans per view.
  Current `.den` text and upstream DSL origins are separate tables.

## Programs and checking in the editor

A `.den` program is a `den.root` folder plus its referenced libraries; a file outside
every root is a standalone program ([format](den-format.md#programs-denroot)). The
editor checks every known program in the background through one serial, fair scheduler
with a warm session per program, and publishes each program's findings on its own files
([protocol](../den/lsp/PROTOCOL.md), [decisions](decisions.md#programs-and-roots)).

## Tests at each layer

- Unit and integration tests per crate (`just test-native`).
- `.den` round trip: the InputMapping regression programs are lowered, printed to
  `.den`, reloaded and checked; structure, origins and default-limit BDD/SAT outcomes
  must match (`test-dsl/tests/ir_text_roundtrip.rs`).
- Editor parity: for every parser-backed regression program, both editors publish the
  same findings (`den/lsp/server/src/publication_tests.rs`).
- LSP scenarios over real stdio (`lsp-tests/`) and installed VS Code smoke tests.
