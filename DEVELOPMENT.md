# Developing Denotate

## Setup

You need [`rustup`](https://rustup.rs) (it installs the toolchain pinned in
`rust-toolchain.toml`), Node 22+ for the VS Code extensions and grammar generation,
and [`just`](https://github.com/casey/just). The VS Code smoke tests need a local
VS Code.

```sh
just                                      # list every recipe
just test-crates                          # IR, checker, sessions, .den library, test DSL
npm ci --prefix den/lsp && just test-den    # .den editor components and LSP scenarios
just check-den den/lsp/examples/library-and-app/app   # check a .den program from the CLI
```

The repository root is one Cargo workspace (`Cargo.toml`, `Cargo.lock`, `target/`)
covering `crates/*`, `test-dsl`, `den/lsp/server` and `lsp-tests`.

To try the `.den` editor, open `den/lsp/` in VS Code and run **Run Denotate semantic
checking** (F5); see [den/lsp/README.md](den/lsp/README.md). The test DSL editor
is in [test-dsl/vscode/](test-dsl/vscode/README.md).

## Verification

```sh
just test-crates
npm ci --prefix den/lsp && just test-den
just test-dsl-lsp
just test-den-vscode && just test-dsl-vscode   # needs local VS Code
cargo +1.93.0 fmt --all --check
```

If a grammar changes, regenerate with the pinned CLI (`npm run generate --prefix
den/lsp`, `just generate-test-dsl`) and commit the generated files; CI checks
that they are current.

## Layout

| Path | What |
| --- | --- |
| `crates/` | Core Rust crates: IR, normalization, checker, sessions, presentation, editor mechanics, `.den` library |
| `den/grammar/` | Tree-sitter grammar of `.den` (generated parser committed) |
| `den/lsp/` | `.den` language server (`server/`) and VS Code extension |
| `test-dsl/` | Test DSL: parser, lowering, export to `.den`, LSP server and VS Code extension |
| `lsp-tests/` | LSP scenario tests run against the `.den` server (and the test DSL, feature-gated) |
| `fixtures/` | Shared `.den` workspaces for editor tests |
| `docs/` | Architecture, `.den` format, decisions, checker policies, roadmap |

## Documentation

- [Architecture](docs/architecture.md): layers and what belongs where.
- [The `.den` format](docs/den-format.md): syntax, namespaces, program roots, origins.
- [Decisions](docs/decisions.md): settled design choices and why.
- [Checker performance policies](docs/checker-policies.md): what is provisional.
- [Roadmap](docs/roadmap.md).
- [Editor protocol](den/lsp/PROTOCOL.md): the `.den` server's custom LSP surface.
