# Facts before component analysis

These completion programs describe a whole-output task and a partial-output task.
The partial task's applicability depends on the whole value, but it cannot write
that whole value itself.

`fact-guards` derives `whole_output` using negation of a fixed `partial_output`
fact. Its rules also test `!conditional_output` where `conditional_output` is a
fact. Those false bodies cannot carry dependencies. `explicit-facts` spells out
the same fixed output shapes directly.

Run either program:

```sh
just check-den fixtures/completion-search-free/fact-guards --engine sat --verbose
just check-den fixtures/completion-search-free/explicit-facts --engine sat --verbose
```

Both have a unique meaning for every input observation and no cyclic analysis
component, with or without `--completion-prune`. The integration test in
`crates/ir-text/tests/completion_checks.rs` asserts both properties. Ground/source
rule slots remain available for provenance; inactive rules are excluded from the
analysis graph.
