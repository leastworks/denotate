# Agent instructions

## Commits

- Do not add `Co-Authored-By` or other AI attribution trailers to commit messages
  or pull request descriptions.
- Use the existing subject style: a short prefix such as `enh:`, then a summary.

## Working rules

- Correctness and usability come before performance. Performance policies are
  provisional until re-scored on real programs ([docs/checker-policies.md](docs/checker-policies.md)).
- Test gates are behavioral: default-limit outcomes, witnesses and diagnostics match;
  cold and warm sessions agree; conclusive answers agree across backends. Budgets,
  receipts, timings and solver-selected witnesses are never goldens.
- Keep layering intact ([docs/architecture.md](docs/architecture.md)): the checker and
  presentation know no LSP or DSL; `native/ir-text` performs no IO outside
  `filesystem`; editors own buffers, discovery and scheduling.
- The editor never treats disk as authoritative when a buffer may be open.

## Verification

```sh
just test-native
npm ci --prefix den/lsp && just test-b
just test-inputmapping-lsp
just test-b-vscode && just test-inputmapping-vscode   # needs local VS Code
cargo +1.93.0 fmt --manifest-path native/Cargo.toml --all --check
cargo fmt --manifest-path Cargo.toml --all --check
```

If a grammar changes, regenerate with the pinned CLI (`npm run generate --prefix
den/lsp`, `just generate-inputmapping`) and commit the generated files; CI checks
that they are current.
