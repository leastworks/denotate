# denotate-presentation

Frontend-independent interpretation of checked evidence. It turns a checker
`Verification` into findings with stable identities, kinds, severities, notes and
participating occurrences, and places them on source locations. It depends only on
`denotate-ir` and `denotate-check`: no LSP, DSL vocabulary, filesystem or scheduling.

- `interpret(corpus, verification)` returns `Finding`s for counterexamples,
  no-meaning regions, unsupported groups and regions, and inconclusive outcomes.
- Coverage produces one finding per obligation/verification, with bounded missing-group
  examples, separate observations, and exact or lower-bound counts. Each example is
  placed on its locatable grouping-constant declarations in the program's own files,
  with obligation fallback if none qualify. Shared primary locations merge group notes.
  Empty grouping domains produce an Information note without turning a proof into a failure.
- Exactly-one uses `Identity::Coverage` and `Identity::Uniqueness` for its two parts;
  component labels distinguish their messages. Uniqueness remains per group. Standalone
  at-most-one retains `Identity::Group` and its existing protocol shape.
- Emptiness uses `Identity::Emptiness` with a bounded set of replay-confirmed tuples,
  each placed on its own retained derivation. Tuple notes restrict the observation
  to checker-supplied structural dependency-cone inputs, including dependencies
  behind derived absences. The full world stays in structured evidence.
  Incomplete analysis stays visible alongside a failure; unknown worlds without a
  witness produce an inconclusive finding.
- Uniqueness and coverage world notes use checker-supplied structural input cones.
  Uniqueness includes the conflicting tuples; coverage includes all candidates of
  each missing group. Empty scopes omit the note; unavailable scopes explicitly
  show the full world. Structured evidence always retains the original observation.
- `Identity` encodes a group, coverage/uniqueness/emptiness component, region or rewrite finding from semantic keys
  (`data(keys)`), never arena IDs or message text.
- `Placement` chooses primary locations from the checked program's **own** files
  (producing rules first, then contributing occurrences, declarations, the
  obligation), with library occurrences and upstream origins as related locations.
  If no own occurrence participates, it produces the labeled fallback
  (`in <program>: …`). Current-text and upstream provenance are separate inputs.
- Library-declared emptiness and uniqueness counterexamples narrow primaries to the
  first locatable own-file producers along retained positive support. Walk through
  unlocated generated rules; never stop at declarations or premise tokens. Union
  per-tuple frontiers, retaining each tuple's fallback independently and keeping
  the full derivation related. Own-file and unlocated obligations keep old placement.
- `rewrites` groups proven rewrite warnings and their coverage; they never carry edits.
- `summary` builds root-level outcome summaries (backend, selected assumptions, group
  and region outcomes, resource reasons).

Frontends adapt the output: `crates/ir-text`'s `presentation` module for `.den`, and
the test DSL presenter, which keeps its own wording, guard locations and
safe-edit eligibility on top of the shared classification.

```sh
cargo +1.93.0 test --locked -p denotate-presentation -p denotate-ir-text
```
