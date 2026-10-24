# Denotate

Denotate is an intermediate representation for **checked business rules**, with an
editor for writing them directly.

- **The IR** is a small relational language: sorts, typed constants, input and derived
  relations, rules with negation, and contracts such as `at_most_one`. Its meaning is
  the least fixed point of the rules for every permitted input world.
- **The checker** proves contracts over all permitted input worlds (finite domains,
  constrained by input assumptions), or returns a replayed counterexample. BDD is the
  default backend; SAT is selectable.
- **`.den`** is the IR's text format, for authoring and for export. A bespoke DSL can
  lower to the IR, print itself as `.den` with embedded `loc(...)` origins, and the
  `.den` editor shows the same findings with links back to the DSL source.
- **The `.den` editor** (a Rust language server plus a VS Code extension) checks every
  program in the workspace in the background, publishes findings with related
  locations, navigates to DSL origins, and renames safely across programs.
- **InputMapping** (`test-dsl/`) is the first DSL built on the IR: a small
  input-to-slot mapping language with its own editor.

## Quick start

Requirements: Rust 1.93.0 and 1.78.0 (`rustup`), Node 22+, and
[`just`](https://github.com/casey/just). The VS Code smoke tests need a local VS Code.

```sh
just test-native                    # IR, checker, sessions, .den library, test DSL
npm ci --prefix den/lsp && just test-b   # .den editor components and LSP scenarios
just check-den den/lsp/examples/library-and-app/app   # check a .den program from the CLI
```

To try the editor, open `den/lsp/` in VS Code and run **Run Denotate semantic
checking** (F5). See [den/lsp/README.md](den/lsp/README.md).

## Layout

| Path | What |
| --- | --- |
| `native/` | Core Rust workspace: IR, normalization, checker, sessions, presentation, editor mechanics, `.den` library |
| `den/grammar/` | Tree-sitter grammar of `.den` (generated parser committed) |
| `den/lsp/` | `.den` language server (`server/`) and VS Code extension |
| `test-dsl/` | InputMapping: parser, lowering, export to `.den`, LSP server and VS Code extension |
| `lsp-tests/` | LSP scenario tests run against the `.den` server (and InputMapping, feature-gated) |
| `fixtures/` | Shared `.den` workspaces for editor tests |
| `docs/` | Architecture, `.den` format, decisions, checker policies, roadmap |

## Documentation

- [Architecture](docs/architecture.md): layers and what belongs where.
- [The `.den` format](docs/den-format.md): syntax, namespaces, program roots, origins.
- [Decisions](docs/decisions.md): settled design choices and why.
- [Checker performance policies](docs/checker-policies.md): what is provisional.
- [Roadmap](docs/roadmap.md).
- [Editor protocol](den/lsp/PROTOCOL.md): the `.den` server's custom LSP surface.

Contributors and agents: see [AGENTS.md](AGENTS.md).
