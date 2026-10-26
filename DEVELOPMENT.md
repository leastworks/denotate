# Developing Denotate

## Setup

You need [`rustup`](https://rustup.rs) (it installs the toolchain pinned in
`rust-toolchain.toml`), Node 22+ for the VS Code extensions and grammar generation,
and [`just`](https://github.com/casey/just). The VS Code smoke tests need a local
VS Code.

```sh
just                                      # list every recipe
just test-crates                          # IR, checker, sessions, .den library, test DSL
npm ci --prefix editors/den && just test-den    # .den editor components and LSP scenarios
just check-den editors/den/examples/library-and-app/app   # check a .den program from the CLI
```

The repository root is one Cargo workspace (`Cargo.toml`, `Cargo.lock`, `target/`)
covering every crate in `crates/`.

To try the `.den` editor, open `editors/den/` in VS Code and run **Run Denotate semantic
checking** (F5); see [editors/den/README.md](editors/den/README.md). The test DSL editor
is in [editors/test-dsl/](editors/test-dsl/README.md).

## Verification

```sh
just test-crates
npm ci --prefix editors/den && just test-den
just test-dsl-lsp
just test-den-vscode && just test-dsl-vscode   # needs local VS Code
cargo +1.93.0 fmt --all --check
```

If a grammar changes, regenerate with the pinned CLI (`npm run generate --prefix
editors/den`, `just generate-test-dsl`) and commit the generated files; CI checks
that they are current.

## Layout

| Path | What |
| --- | --- |
| `crates/` | All Rust: IR, normalization, checker, sessions, presentation, editor mechanics and the `.den` library; `den-lsp` (the `.den` language server), `test-dsl` (the example DSL, with its server) and `lsp-tests` (LSP scenarios) |
| `editors/` | VS Code clients: `den` (the `.den` editor, with examples) and `test-dsl` |
| `grammars/` | Tree-sitter grammars `den` and `test-dsl` (generated parsers committed) |
| `fixtures/` | Shared `.den` workspaces for editor tests |
| `docs/` | Architecture, `.den` format, decisions, checker policies, roadmap |

## Documentation

- [Architecture](docs/architecture.md): layers and what belongs where.
- [The `.den` format](docs/den-format.md): syntax, namespaces, program roots, origins.
- [Decisions](docs/decisions.md): settled design choices and why.
- [Checker performance policies](docs/checker-policies.md): what is provisional.
- [Roadmap](docs/roadmap.md).
- [Editor protocol](crates/den-lsp/PROTOCOL.md): the `.den` server's custom LSP surface.
