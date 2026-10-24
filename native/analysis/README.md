# denotate-analysis

Salsa-based rule analysis reused by the `.den` editor index (`native/ir-text/src/index`).
It provides rule-local linting from resolved evidence: unsafe variables (head or
negation without positive-body support), singleton variables, arity and sort evidence,
and input-definition checks (`analyze_resolved_rule`, `RuleAnalysis`, `AtomEvidence`).

Name resolution for `.den` is not here: it lives in `ir-text`'s index, shared with the
strict loader. The crate also contains an older module/file-based declaration and
argument analysis from an earlier editor prototype; nothing outside the crate uses it
today, so it is a candidate for trimming.

```sh
cargo +1.93.0 test --manifest-path native/Cargo.toml --locked -p denotate-analysis
```
