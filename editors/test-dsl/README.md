# The test DSL in VS Code

The VS Code extension for the [test DSL](../../crates/test-dsl/README.md). It starts the Rust
`test-dsl-lsp` server over stdio; JavaScript provides only VS Code registration and
the language client.

## Try it

With rustup, Node 22+, just and VS Code's `code` launcher installed, run from the
repository root:

```sh
just edit-test-dsl editors/test-dsl/examples
```

The command prepares pinned dependencies, builds the client and release server,
and opens the examples with the extension. Repeat runs reuse unchanged dependencies.
`just build-test-dsl` builds without opening VS Code; `just setup-test-dsl --force`
reinstalls dependencies. The **Run test DSL** F5 configuration also uses the same
build recipe.

- `overlap.testdsl`: both `b` targets conflict. Hover them or open **Problems**
  for the conflicting inputs, quoted conditions and an example observation; related
  information jumps to each input and mapping.
- Add `mask b;`: the conflict clears without deleting mappings. `mask b when
  available(a);` also clears it here; combining both shows a coverage warning.
- Change `available(a)` to `available(missing)`: a name error pauses checking until
  repaired.
- `values.testdsl`: integer guards and mutually exclusive conditions that negate each other;
  hover a redundant negation to see why it can be removed.
- `input input_a; slot a; a <- input_a when not available(a);` reports that there is no
  consistent result whenever `input_a` is present.

Each open file is a separate program. New edits withdraw old findings immediately;
results arrive from the background worker for the current snapshot only. Highlighting,
comment toggling and brackets are configured; completion, navigation, rename and code
actions are not implemented yet.

## Check it

```sh
just test-dsl-extension   # package and example checks (no GUI)
just test-dsl-vscode      # installed VS Code smoke (needs a local VS Code)
```
