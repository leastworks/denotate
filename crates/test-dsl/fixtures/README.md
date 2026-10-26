# Test DSL fixtures

| Path | Contents |
| --- | --- |
| `corpus.txt` | The regression corpus: hand-written programs separated by `---`, named `corpus/NN` by position. Tests also use generated cases from `tests/support/normalization_cases.rs` (`generated/NN`). Read both through `tests/support/corpus.rs`. |
| `expected/corpus-NN.json` | Expected behavior of each corpus program: diagnostics, obligation groups, and the facts of every small input world (worlds the input assumptions exclude are marked `"permitted": false`). |
| `lowering.txt`, `overlapping-mappings.txt` | Programs for parser, lowering and editor tests. |

The corpus feeds the `.den` round trip, editor parity, session and backend
comparisons, which check paths against each other, and the expectation test
(`src/server/expectations.rs`), which checks behavior against the files above. That
test requires cached and uncached lowering to agree before comparing.

Expectations leave out implementation choices: generated helper relations are not
part of world facts, and diagnostics built from a checker-selected witness (an
overlap counterexample or a no-meaning observation) become one entry per finding in
`witness_findings`, with only code, severity and evidence kind; the witness decides
their wording, ranges and how many highlights a finding gets. The world facts already pin whether such a finding exists; the
checker validates witnesses by replay, and witness wording is tested separately.

When behavior changes on purpose, regenerate and review:

```sh
just update-test-dsl-expectations
git diff crates/test-dsl/fixtures/expected
```

An unexpected expectation diff is a finding to explain, never something to accept by
regenerating. Adding a corpus program adds an expectation file; review it as you would
a hand-written assertion.
