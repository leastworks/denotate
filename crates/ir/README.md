# denotate-ir

The relational IR: typed construction, namespaces, occurrence identities, source
provenance and semantic keys. Plain Rust; its only workspace dependency is
`denotate-normalize`.

## Construction

`Corpus` builds sorts, constants, named-parameter input and derived relations,
conjunctive signed rules, facts, grouped `at_most_one` / `at_least_one` / `exactly_one`
obligations and ungrouped `empty` obligations. Grouping columns are selected by name
or index; message templates are not rendered by the IR. Constructors
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

`empty` / `empty_in` create an ungrouped `Requirement::Empty`; the construction API
takes no grouping argument.

`exactly_one` / `exactly_one_in` create one `Requirement::ExactlyOne` declaration.
`Requirement::kind()` exposes its `Cardinality`; its coverage and uniqueness parts are
checked independently. The same namespace, name and grouping validation applies to all
three constructors.

`Corpus::restrict_input(input, provider)` attaches a derived domain provider after
both signatures are declared. It checks arity and positional sorts immediately;
`validate_input_domains()` checks the completed rule graph for input dependencies
and cycles through negation. The checker repeats this validation with bounded work
before evaluation. The attachment is `Relation::input_domain`; semantic schemas
carry the provider's relation key. Parameter names need not match.

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

Named assumptions use the same `Restriction` cardinality shape as `Requirement`:
`assume_at_most_one_in`, `assume_at_least_one_in`, `assume_exactly_one_in` and
`assume_empty_in` (or `assume_in`). Input and derived targets are allowed. Once rules
are complete, `validate_assumptions` rejects dependency cycles through negation;
positive recursion and input dependencies are allowed. This validation cannot use
the assumptions it validates. The checker owns evaluation and consistency.
