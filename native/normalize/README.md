# denotate-normalize

Dependency-free Boolean normalization of a `Definition<H, L, K>`: an opaque head with
argument keys and an optional Boolean body. The result is an immutable recipe that
frontends cache and install into a fresh `Corpus` (`denotate_ir::installation`).

**Semantics:** classical double-negation cancellation, then Lloyd–Topor with
linear-size helpers. Root OR alternatives become separate rules, positive conjunctions
flatten, negated ORs use De Morgan, and negated conjunctions or nested positive ORs use
helper definitions. This is a deliberate choice, not a semantics-preserving translation
of arbitrary recursive nested stable-model expressions: `p :- not not p` becomes
`p :- p`.

- Every head, expression node and argument needs a unique statement-local key; a `None`
  body is a fact. `Recipe::records` reports source nodes, applied negations, polarity,
  helper definition/use roles and OR branch paths, so frontends choose their own
  attribution policy.
- Ground expressions are fully supported. If a helper's defining expression contains
  any variable, normalization returns `HelperCapturesVariables`; it never invents an
  existential scope. Parameterized helpers are deferred.
- Namespace binding happens at installation (`install_in`), so recipes are reusable
  across namespaces and files.

Tests include an independent stable-model oracle over every expression with up to six
nodes and two input leaves, in all four worlds.

```sh
cargo +1.93.0 test --manifest-path native/Cargo.toml --locked -p denotate-normalize -p denotate-ir
```
