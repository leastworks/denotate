# LSP scenario tests

Rust tests that drive a real language server over stdio (`tests/support/mod.rs`
starts it in a temporary copy of a `fixtures/` workspace, with `DENOTATE_TEST_MODE=1`).

- By default the server is the `.den` editor's `den/lsp/dist/denotate-lsp`; build it
  first (`npm run build --prefix den/lsp`). `just test-den` builds and runs every
  scenario.
- `DENOTATE_LSP_COMMAND` / `DENOTATE_LSP_ARGS` select another server. The test DSL
  scenarios (`tests/test_dsl.rs`) are feature-gated and run with
  `just test-dsl-lsp`.
- `tests/latency.rs` is an ignored, manual latency smoke with no thresholds
  (`just bench-lsp`).

It is a member of the repository's single Cargo workspace.
