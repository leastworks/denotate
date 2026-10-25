# The `.den` editor

A Rust language server (`server/`, crate `denotate-lsp`) and a VS Code extension
(`src/extension.cjs`) for the [`.den` format](../../docs/den-format.md). Language
semantics come from `crates/ir-text`; this package owns the editor: program
discovery, buffers, background checking, publication, navigation and rename.

## Try it

```sh
npm ci --prefix den/lsp
code den/lsp
```

In Run and Debug choose a launch configuration and press **F5**; the build runs first.

- **Run Denotate semantic checking** opens `examples/semantic-checking/`: two facts
  violate an obligation. Comment one out to clear the findings; unsaved edits are
  checked. Hover the status bar item for the program, checking state, backend and
  active assumptions.
- **Run Denotate library and app** opens `examples/library-and-app/`: the library
  holds the obligation and an assumption, the app supplies facts. Comment out the
  assumption to see the conflict on the app's facts, with related locations in the
  library; the library file itself stays clean.
- **Run Denotate (language services)** opens the shared `fixtures/base/00-valid/`
  workspace for outline, navigation, completion, hover, rename and formatting.

To see DSL origins, export an InputMapping program and open the output folder:

```sh
just export-inputmapping /tmp/example-den test-dsl/vscode/examples/overlap.inputmapping
```

Findings on the exported `.den` carry related locations into the `.inputmapping`
source; **Denotate: Go to Origin** jumps there (hash-checked; a changed source is
reported, not navigated). Do not commit generated exports: they contain absolute
`file://` URIs.

## What the editor does

- **Programs.** Discovers every `den.root` in the workspace and referenced libraries;
  each file has one home program. A file outside every root is a standalone program
  with **Create den.root here** quick fixes.
- **Editor services** for the full grammar: diagnostics, outline, definition,
  references, completion, hover, signature help, semantic tokens and formatting.
- **Checking.** Every program is checked in the background (BDD by default; set
  `denotate.backend` to `sat`), with one warm session per program and fair serial
  scheduling. Results publish only if they still match the current snapshots.
- **Go to Origin** for occurrences with embedded origins.
- **Rename** validated across every affected program, including unopened library
  consumers.

The custom protocol (root status, manifest sync, origin snapshots, test hooks) is in
[PROTOCOL.md](PROTOCOL.md).

## Tests

```sh
just test-b          # server component tests, syntax manifest, all shared LSP scenarios
npm run test:origins --prefix den/lsp   # Go to Origin unit tests
just test-b-vscode   # installed VS Code smoke (needs a local VS Code)
```

`npm run build` regenerates the parser from `den/grammar` with the pinned
`tree-sitter-cli`, builds the release server and bundles the extension into `dist/`.
