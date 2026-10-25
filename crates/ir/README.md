# denotate-ir

The relational IR: typed construction, namespaces, occurrence identities, source
provenance and semantic keys. Plain Rust; its only workspace dependency is
`denotate-normalize`.

## Construction

`Corpus` builds sorts, constants, named-parameter input and derived relations,
conjunctive signed rules, facts and `at_most_one` obligations (grouping columns by
name or index, with a message template that the IR does not render). Constructors
return `ConstructionError` for foreign handles, duplicate or empty names, arity and
sort mismatches, inconsistent variable sorts, unsafe head or negative variables,
input definitions and invalid grouping columns. Variables are rule-local; duplicate
authored facts keep separate occurrences.

- **Namespaces.** `*_in` constructors take a `Namespace` path of decoded, non-empty
  segments (`Namespace::new(["billing", "invoices"])?`, which differs from the single
  segment `"billing::invoices"`); `Namespace::default()` is global. Rules and generated
  helpers have an explicit owning namespace, independent of the declarations they
  reference. `Corpus::namespace(id)` returns it.
- **Generated helpers.** `declare_generated_relation*` creates zero-arity derived
  helpers of a separate kind (`is_generated_relation`), never aliasing a frontend
  relation with the same label.
- **Recipe installation.** `installation::install_in(corpus, namespace, recipe, …)`
  binds an arena-free normalization recipe to current relations and terms and returns
  fresh occurrence maps; `transfer` attaches frontend-chosen provenance. The same
  cached recipe installs into any namespace.
- `top_level(&corpus)` enumerates the occurrences that need file placement on export.

Construction validity does not imply admissibility; checking is `denotate-check`.

## Occurrences, sources and provenance

- Declaration handles identify semantic declarations. Every atom and term use has its
  own `OccurrenceId`. Handles are opaque and arena-stamped: process-local, never
  persistent identities.
- `Sources` holds immutable URI/revision/view/text snapshots. `SourceSpan` is a checked
  half-open UTF-8 byte range; LSP conversion belongs to editors and uses the
  referenced snapshot.
- `Provenance` maps occurrences to one or more origins, separately from the corpus.
  Views (for example `denotate` or a DSL's view) let a presenter choose locations; no
  semantic identity contains a source offset.
- `SemanticKeys` bind stable, name-based keys to declarations, rules and occurrences
  for caching and result correspondence across snapshots.

## Tests

```sh
cargo +1.93.0 test --locked -p denotate-ir
```
