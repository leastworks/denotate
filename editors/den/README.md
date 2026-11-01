# The `.den` editor

A Rust language server (`server/`, crate `denotate-lsp`) and a VS Code extension
(`src/extension.cjs`) for the [`.den` format](../../docs/den-format.md). Language
semantics come from `crates/ir-text`; this package owns the editor: program
discovery, buffers, background checking, publication, navigation and rename.

## Try it

```sh
npm ci --prefix editors/den
code editors/den
```

In Run and Debug choose a launch configuration and press **F5**; the build runs first.

- **Run Denotate semantic checking** opens `examples/semantic-checking/`: two facts
  violate an obligation. Comment one out to clear the findings; unsaved edits are
  checked. Hover the status bar item for the program, checking state, backend and
  per-verification assumptions and outcomes.
- **Run Denotate library and app** opens `examples/library-and-app/`: the library
  holds the obligation, an assumption and `library::default_checks`; the app supplies
  facts and `mappings::unrestricted_inputs`. The library verification proves uniqueness
  in both programs. The app's unrestricted verification reports overlapping facts.
  Add `library::one_present_input` to the app verification's `assumptions` list to
  clear that conflict, then remove it to restore it. Editing the library verification
  to `assumptions: []` exposes the app conflict in that context too; the library-alone
  program remains clean because it has no mappings. Deleting a referenced assumption
  instead produces a reference error.
- **Run Denotate (language services)** opens the shared `fixtures/base/00-valid/`
  workspace for outline, navigation, completion, hover, rename and formatting.

To see DSL origins, export a test DSL program and open the output folder:

```sh
just export-test-dsl /tmp/example-den editors/test-dsl/examples/overlap.testdsl
```

Findings on the exported `.den` carry related locations into the `.testdsl`
source; **Denotate: Go to Origin** jumps there (hash-checked; a changed source is
reported, not navigated). Do not commit generated exports: they contain absolute
`file://` URIs.

The [Shipping News tutorial](examples/shipping-news/README.md) builds a complete
message-mapping and classification example in nine runnable steps.

## What the editor does

- **Programs.** Discovers every `den.root` in the workspace and referenced libraries;
  each file has one home program. A file outside every root is a standalone program
  with **Create den.root here** quick fixes.
- **Editor services** for the full grammar: diagnostics, outline, definition,
  references, completion, hover, signature help, semantic tokens and formatting.
  Verification lists navigate to their assumptions and obligations; completion offers
  only the appropriate kind. Validated rename follows those references through every
  affected program, including consumers of a library.
- **Checking.** Each program checks all included verifications in the background
  (BDD), with one warm session per program
  and fair serial scheduling. Results publish atomically only if they still match
  current snapshots. Without a verification, status is **No verification configured**
  and semantic checking is disabled. Unselected obligations receive Information
  notices; empty obligation lists receive a consistency-only Warning.
- **Go to Origin** for occurrences with embedded origins.
- **Rename** validated across every affected program, including unopened library
  consumers.

The custom protocol (root status, manifest sync, origin snapshots, test hooks) is in
[PROTOCOL.md](../../crates/den-lsp/PROTOCOL.md).

## Tests

```sh
just test-den          # server component tests, syntax manifest, all shared LSP scenarios
npm run test:origins --prefix editors/den   # Go to Origin unit tests
just test-den-vscode   # installed VS Code smoke (needs a local VS Code)
```

`npm run build` checks the parser from `grammars/den`, builds the release server
and bundles the extension into `dist/`. Parser generation uses a local content
fingerprint in `target/den-parser-generation.json`: the grammar, tree-sitter
configuration, pinned generator executable/version, Node version and generation
script. It also checks the generated files' contents; missing or modified outputs
trigger regeneration. The grammar is self-contained; any future imported helper
must be added to the script's input list.

Generation runs in a temporary directory and copies back only changed files, so
identical output keeps its timestamps and does not invalidate Cargo's parser build.
A missing cache is harmless. Failed generation preserves the old outputs and cache.
`npm run generate -- --force` bypasses the cache; CI uses this before checking that
the committed parser is current. `npm run test:generation` tests these behaviors
with isolated grammars and the pinned generator.

`just edit-den <folder>` uses this same build. With unchanged inputs, parser generation
is skipped and Cargo reuses the server; extension bundling and copying still run.
