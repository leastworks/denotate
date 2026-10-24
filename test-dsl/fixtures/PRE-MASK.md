# Frozen InputMapping regression corpora

These files are independent baselines. Do not regenerate them to make a failure pass.

| File | Contents | Used by |
| --- | --- | --- |
| `pre-mask.json` | 22 cases captured before conditional masking: the original checking examples and every mapping in `lowering.txt`, each with its exact source | server regression test (`src/server/premask.rs`), check-session tests, `.den` round trip and editor parity |
| `pre-mask-sources.json` | SHA-256 pins for `pre-mask.json` and each embedded source | the extension package test |
| `pre-normalize.json` | Cases captured before shared Boolean normalization | `src/server/prenormalize.rs`, normalization tests, round trip and parity |
| `pre-integration-fingerprints.json` | 84 installed-IR fingerprint cases with sources and revisions | normalization tests, round trip and parity |

`pre-mask.json` was captured at runtime revision
`85fac25ae5c2bff8479e2b942c3b71d526fb9e9d` of the original prototype repository.

The pre-mask comparison checks ground rules, dependencies, obligation groups, every
small input world, settled and blocked facts, replay evidence and completeness, plus
final diagnostics (kind, severity, wording, primary and related ranges). Identities are
names, authored rule indices and component atoms, never arena stamps. The only
normalization since the capture is the library's `!masked(Slot)` premise on `supplies`:
the test requires it on each instance with no possible producer, and removes exactly
that premise and its `NoPossibleProducer` evidence before comparing.

The historical capture commands are not kept; the corpora are fixed inputs.
