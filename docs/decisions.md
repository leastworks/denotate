# Decisions

Settled design choices and why they were made. Current behavior is specified in the
[`.den` format](den-format.md), the [architecture](architecture.md) and the
[editor protocol](../crates/den-lsp/PROTOCOL.md); this page records the reasons and the
alternatives that were rejected. Revisit a decision only with new evidence, such as a
real program that the current choice serves badly.

## Meaning and checking

- **Negation is admitted by justification, not by stratification.** Business DSLs
  naturally define mutually exclusive cases that negate each other. Relation-level
  stratification would reject them, so the checker proves such negations redundant
  under the assumptions, or certifies a world, and reports everything else as
  unsupported or no-meaning ([meaning](den-format.md#meaning)).
  The well-founded semantics is not adopted until a real program needs it.
- **Conclusive answers must be sound.** A false counterexample or a silent success
  misleads the author; an explicit inconclusive or unsupported outcome does not. Hence
  counterexamples only after concrete replay (or certification), and SAT's
  unfounded-support world is never presented as an overlap witness.
- **Assumptions take effect only through an explicit verification.** Assumptions are
  the domain constraints a library author chooses. When every declared assumption was
  active, declaring or importing one silently changed every check, and one obligation
  could not be checked under two sets of assumptions. A verification names its
  context, so the author's choice is visible and the same obligation can be checked
  under several contexts.
- **No verification, no semantic checking.** Any implicit context (unrestricted inputs,
  or all assumptions) would be a choice the author never made, and could report a
  library as wrong, or as proved, for inputs it was never meant to accept. The
  editor and `check-den` say "unconfigured" instead.
- **Analysis is per verification.** Admission, rewrite proofs and no-meaning findings
  depend on the permitted worlds, so they are computed for each verification, never
  once for the program and reused. Finding identities include the verification, so
  two verifications of one obligation never overwrite or deduplicate each other.
- **Coverage ranges over resolved domains.** Enumerating only groups with producing
  tuples would silently miss missing assignments. `at_least_one` therefore includes
  all grouping-domain combinations, including overrides. Enumeration is bounded;
  exhaustion remains explicit, with known failures preserved. An empty grouping
  domain proves coverage vacuously but gets an Information note to expose accidental
  empty scope. Empty grouping itself still creates one global group.
- **Coverage failures are aggregated; uniqueness failures remain per group.** One
  diagnostic per missing domain combination could flood an obligation declaration.
  Coverage therefore retains a bounded sample and an exact count or explicit lower
  bound. Its identity depends on the obligation, component and verification, never
  on sample selection. Each example retains its own input world.
- **Correctness and usability before performance.** Performance policies are
  provisional until re-scored on real programs ([checker policies](checker-policies.md)).
- **Budgets, receipts, timings and witness choices are not goldens.** They change
  whenever a provisional policy changes. Tests compare outcomes, identities,
  diagnostics and cold/warm equality.

## The `.den` format

- **`.den` is both an authoring and an export format**, MLIR-style: plain files with
  embedded `loc(...)` origins that reload into the same program.
- **C#-style namespaces, independent of files.** Nested, reopenable, spanning files;
  `use` is visibility only. Qualified paths are absolute; inner names do not shadow
  outer ones (ambiguity is an error). Relaxing shadowing later would be compatible;
  relative paths would not, so they were rejected.
- **No `order N`.** Cross-file rule interleaving has no meaning and is not transported.
- **Identity is independent of files and positions**, so moving, reformatting or
  splitting files does not change cached results or finding identities.
- **Origins identify sources by content** (URI, view, SHA-256), so a changed source is
  detected rather than navigated to the wrong place.

## Programs and roots

- **`den.root` JSON manifests define programs.** Kept as JSON rather than `.den` syntax
  to keep membership separate from program text.
- **No implicit roots.** A workspace-folder root would exist only in the editor, so the
  editor and `check-den` would check different programs. A file outside every
  `den.root` is a standalone program instead, with a quick fix to create a root.
- **Every program is checked; there is no "active root" selection.** Because scanning
  stops at nested roots, each file already has exactly one owning root, its home
  program. A selection could only choose which consumer's results a shared library
  file displays, making its diagnostics depend on hidden per-document state that every
  switch would withdraw and republish. Instead each consumer's results appear on its
  own files, and the library file shows the library checked alone. This replaced an
  earlier design with an explicitly selected active root per document.
- **Included verifications run in every consumer; consumers only add.** A library's
  verification states a contract that each consumer must meet with its own facts, so
  it runs in every program that includes it and cannot be overridden or weakened by
  a consumer, which may only add verifications of its own.
- **Unchecked obligations are noticed, including in libraries.** Moving from implicit
  to explicit selection creates a new silent failure: an obligation nothing checks.
  Each program reports every obligation in its closure that no verification selects,
  at the declaration (through the labeled fallback for library files), as information
  rather than as a finding.
- **A finding belongs to the program whose check produced it.** When a consumer's
  finding involves none of its own files, it is published on the library location,
  labeled with the consumer, rather than lost; it is not deduplicated, because each
  consumer checks the library under its own facts and assumptions. Likewise a consumer
  declaration that makes a library name ambiguous is reported on the consumer, since
  the library checked alone has no such failure.

## The editor

- **Warm sessions survive temporary breakage.** A program with a syntax error is
  blocked but keeps its checker session, so typing does not cost a cold check; only
  removing the root releases it.
- **Rename is validated by re-resolving, not by a reference list.** A dry run over
  every affected program catches capture, new ambiguity and structural changes that a
  list of references cannot.
