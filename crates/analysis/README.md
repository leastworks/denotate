# denotate-analysis

Salsa-based rule analysis reused by the `.den` editor index (`crates/ir-text/src/index`).
It provides rule-local linting from resolved evidence: unsafe variables (head or
negation without positive-body support), singleton variables, arity and sort evidence,
and input-definition checks (`analyze_resolved_rule`, `RuleAnalysis`, `AtomEvidence`).

Name resolution for `.den` is not here: it lives in `ir-text`'s index, shared with the
strict loader. The crate also contains an older module/file-based declaration and
argument analysis from an earlier editor prototype; nothing outside the crate uses it
today; trimming it is on the [roadmap](../../docs/roadmap.md#small-items).

```sh
just test-crate denotate-analysis
```
