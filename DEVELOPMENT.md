# Developing Denotate

## Setup

You need [`rustup`](https://rustup.rs) (it installs the toolchain pinned in
`rust-toolchain.toml`), Node 22+ for the VS Code extensions and grammar generation,
and [`just`](https://github.com/casey/just). The VS Code smoke tests need a local
VS Code.

```sh
just                         # list every recipe
just setup                   # prepare the pinned Rust toolchain and both editors
just test-crates             # IR, checker, sessions, .den library, test DSL
just test-den                # prepares dependencies, then tests the .den editor
just check-den editors/den/examples/library-and-app/app   # check a .den program from the CLI
```

The repository root is one Cargo workspace (`Cargo.toml`, `Cargo.lock`, `target/`)
covering every crate in `crates/`.

Editor commands install the pinned npm dependencies when missing or changed; repeat
runs reuse them. `just setup-den --force` and `just setup-test-dsl --force` reinstall
an editor's dependencies if needed. No separate npm commands are required.
`just` is the command-line interface; recipes and F5 tasks share the same npm build
scripts, whose `prebuild` hooks prepare dependencies automatically.

Try `just edit-den editors/den/examples/semantic-checking` or
`just edit-test-dsl editors/test-dsl/examples`; see the
[`.den` editor](editors/den/README.md) and [test DSL editor](editors/test-dsl/README.md)
for their example workspaces.

To work on `.den` programs kept outside this repository, run `just edit-den <folder>`:
it builds the editor and opens that folder in VS Code with the extension from this
checkout. Parser generation skips unchanged inputs and preserves unchanged output
files so Cargo can reuse the server build; see the [build details](editors/den/README.md#tests).
Open the folder containing all of a program's `den.root` roots.

## Verification

```sh
just verify          # correctness tests, including scorecards, and formatting; no GUI
just verify-vscode   # both installed VS Code smokes when needed, one at a time
```

The individual recipes (`just test-crates`, `just test-den`, `just test-dsl-lsp`,
`just test-dsl-extension`, `just fmt-check`) remain available for focused work.
Use `just test-crate denotate-check` for one crate and `just fmt` to format Rust.

Use focused tests during implementation, then run `just verify` once for the
completed code change. After a small follow-up fix, rerun the affected tests;
repeat the full gate only when the change or an unresolved failure warrants it.
Documentation and sample-only changes need their relevant link, example or
tutorial checks, rather than the full code gate.

The scorecards' correctness tests run in the normal test profile as part of
`verify`; `just test-scorecards` runs them separately for focused work. They check
outcome agreement, cold/warm and edited/fresh behavior, instrumentation and report
contents. They do not enforce timing or memory thresholds. Run release scorecards
and benchmarks when evaluating a performance claim, on a relevant workload.
Reuse the workspace's `target/` directory unless isolation is necessary.

Run the affected editor's installed smoke (`just test-den-vscode` or
`just test-dsl-vscode`) when activation, packaging, client behavior or editor
integration changes. Pure checker changes normally rely on the gate's LSP and
publication tests. Run both smokes before a release or after changes affecting
both extensions. On macOS, run GUI smokes outside the sandbox and sequentially.

If a grammar changes, run `just generate-den` or `just generate-test-dsl` and commit
the generated files. `just generate-den --force` bypasses the local parser cache;
CI forces generation to check that the committed files are current.

## Profiling

For CPU hot spots, sample the CLI instead of adding trace points. The recipes build
the `profiling` Cargo profile (release code with line tables, in `target/profiling`)
and record it with [samply](https://github.com/mstange/samply)
(`brew install samply` or `cargo install --locked samply`):

```sh
just profile-den ROOT [CHECK ARGS...]                 # record, then open the Firefox Profiler
just profile-den-save OUT.json.gz ROOT [CHECK ARGS...] # record only
samply load OUT.json.gz                               # view a saved recording later
```

Paths are relative to the repository root, as with `just check-den`. The viewer shows
a flame graph, an inverted call tree (self time) and a timeline, with Denotate's
function names, inlined frames and source lines. The CLI's own exit status is
reported, not treated as a recipe failure, so incomplete or failing checks can be
profiled. On Linux, sampling may first need
`sudo sysctl kernel.perf_event_paranoid=1`.

Sampling shows which code is hot. The CLI's progress output and
`--profile-memory FILE` show which part of the program (phase, component, rule)
the time and memory belong to; use them together. A saved recording includes the
command line and local paths: for private programs, share findings such as the top
functions by self time, not the file.

To generate a synthetic Shipping News format tree and measure the actual CLI, use
`just bench-den-schema`. Its [benchmark guide](crates/ir-text/examples/schema/README.md)
documents the semantic presets, scaling controls, optional CPU sampling and persistent
reports, including incomplete runs. It builds before measurement and keeps checker
limits explicit.

## Layout

| Path | What |
| --- | --- |
| `crates/` | All Rust: IR, normalization, checker, sessions, presentation, editor mechanics and the `.den` library; `den-lsp` (the `.den` language server), `test-dsl` (the example DSL, with its server) and `lsp-tests` (LSP scenarios) |
| `editors/` | VS Code clients: `den` (the `.den` editor, with examples) and `test-dsl` |
| `grammars/` | Tree-sitter grammars `den` and `test-dsl` (generated parsers committed) |
| `fixtures/` | Shared `.den` workspaces for editor tests |
| `docs/` | Architecture, `.den` format, decisions, checker policies, roadmap |

## Documentation

Start with [Shipping News](editors/den/examples/shipping-news/README.md) for a runnable
tutorial on lowering a DSL to `.den`. Steps 1–9 build a complete mapping example;
lesson 10 models computed values feeding task conditions. The illustrative DSL has
no parser or UDF runtime.

- [Architecture](docs/architecture.md): layers and what belongs where.
- [The `.den` format](docs/den-format.md): syntax, namespaces, program roots, origins.
- [Decisions](docs/decisions.md): settled design choices and why.
- [Checker performance policies](docs/checker-policies.md): what is provisional.
- [Roadmap](docs/roadmap.md).
- [Editor protocol](crates/den-lsp/PROTOCOL.md): the `.den` server's custom LSP surface.
