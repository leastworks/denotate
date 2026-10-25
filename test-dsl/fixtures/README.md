# InputMapping fixtures

| Path | Contents |
| --- | --- |
| `corpus.txt` | The regression corpus: hand-written programs separated by `---`, named `corpus/NN` by position. Tests also use generated cases from `tests/support/normalization_cases.rs` (`generated/NN`). Read both through `tests/support/corpus.rs`. |
| `expected/corpus-NN.json` | Expected behavior of each corpus program: diagnostics, obligation groups and the facts of every small input world. |
| `lowering.txt`, `overlapping-mappings.txt` | Programs for parser, lowering and editor tests. |

The corpus feeds the `.den` round trip, editor parity, session and backend
comparisons, which check paths against each other, and the expectation test
(`src/server/expectations.rs`), which checks behavior against the files above. That
test requires cached and uncached lowering to agree before comparing.

When behavior changes on purpose, regenerate and review:

```sh
just update-inputmapping-expectations
git diff test-dsl/fixtures/expected
```

An unexpected expectation diff is a finding to explain, never something to accept by
regenerating. Adding a corpus program adds an expectation file; review it as you would
a hand-written assertion.
