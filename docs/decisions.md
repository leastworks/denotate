# Decisions

Settled design choices, with the reason for each. Revisit one only with new evidence,
such as a real program that the current choice serves badly.

## Meaning and checking

- **Meaning is the least fixed point for every input world.** A program's meaning is
  defined per permitted input world (finite domains, constrained by the active
  assumptions W). A cycle through negation is admitted only when a justified rewrite
  removes the negation (for example mutually exclusive guards) or a particular world's meaning is certified; otherwise it is reported
  as unsupported, or as no-meaning when some world has no consistent result.
- **Conclusive answers must be sound.** A counterexample is reported only after
  concrete replay (or certification) confirms it. SAT's unfounded-support world is
  never presented as an overlap witness. Inconclusive and unsupported outcomes are
  reported explicitly, never as success.
- **Correctness and usability before performance.** Performance policies are
  provisional until re-scored on real programs ([checker policies](checker-policies.md)).
- **Budgets, receipts, timings and witness choices are not goldens.** Tests compare
  outcomes, identities, diagnostics and cold/warm equality.

## The `.den` format

- **`.den` is both an authoring and an export format**, MLIR-style: plain files with
  embedded `loc(...)` origins that reload into the same program.
- **C#-style namespaces, independent of files.** Nested, reopenable, spanning files;
  `use` is visibility only. Qualified paths are absolute; inner names do not shadow
  outer ones (ambiguity is an error). Relaxing shadowing later would be compatible;
  relative paths would not, so they were rejected.
- **No `order N`.** Cross-file rule interleaving has no meaning and is not transported.
- **Identity is independent of files and positions** (namespace path, kind, resolved
  structure, duplicate ordinal).
- **Origins identify sources by content** (URI, view, SHA-256), with Unicode scalar
  columns and no normalization, so a changed source is detected rather than navigated.

## Programs and roots

- **`den.root` JSON manifests define programs.** Folder membership, nested roots stop
  the scan, libraries are referenced explicitly. Kept as JSON (rather than `.den`
  syntax) to keep membership separate from program text.
- **No implicit roots.** A file outside every `den.root` is a labeled standalone
  program, with a "Create den.root here" quick fix. The editor and `check-den` share
  one membership rule.
- **Home-program model.** Every `.den` file is user-owned by exactly one root, its
  nearest manifest. The editor checks **every** known program and publishes a
  program's findings only on its own files; there is no "active root" selection.
  Primary locations are in the checked program's own files; library code and DSL
  origins are related locations.
- **Labeled library fallback.** If a consumer's finding involves none of its own files,
  it is published on the library location labeled `in <program>: …`. Such findings
  are not deduplicated across programs (one library bug can appear once per consumer).
- **Consumer-caused failures belong to the consumer.** For example, a consumer
  declaration that makes a library name ambiguous is reported on the consumer.

## The editor

- **One resolver for every file.** The editor uses the same index as the strict loader.
- **Buffers are authoritative.** Unsaved manifests and open DSL buffers come from the
  client; a failed lookup never falls back to disk. A matching file on disk never
  masks different buffer text.
- **Warm sessions survive temporary breakage.** A program with a syntax error is
  blocked (findings withdrawn) but keeps its checker session; only removing the root
  releases it.
- **Rename is validated.** A dry run re-resolves every affected program, including
  unopened library consumers, and refuses capture, new ambiguity or structural
  changes. Replacement names use the printer's spelling rules.
- **Shared mechanics, separate policy.** The scheduler, server loop, lifecycle and
  workspace-edit helpers are shared by both editors; what "current" means, ownership
  and wording stay in each frontend.

## Refactoring by equivalence (direction)

Drastic refactorings should be validated by semantic equivalence: least fixed points
over all permitted worlds, projected onto an author-declared observable interface.
See the [roadmap](roadmap.md#refactoring-by-semantic-equivalence).
