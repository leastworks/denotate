# InputMapping in VS Code

The VS Code extension for the [InputMapping test DSL](../README.md). It starts the Rust
`inputmapping-lsp` server over stdio; JavaScript provides only VS Code registration and
the language client.

## Try it

From the repository root (Node 22+ and Rust 1.93.0):

```sh
npm ci --prefix test-dsl/vscode
code test-dsl/vscode
```

Press **F5** and choose **Run InputMapping**. The build bundles the client and copies
the release server. The Extension Development Host opens `examples/`.

- `overlap.inputmapping`: both `b` targets conflict. Hover them or open **Problems**
  for the conflicting inputs, quoted conditions and an example observation; related
  information jumps to each input and mapping.
- Add `mask b;`: the conflict clears without deleting mappings. `mask b when
  available(a);` also clears it here; combining both shows a coverage warning.
- Change `available(a)` to `available(missing)`: a name error pauses checking until
  repaired.
- `values.inputmapping`: integer guards and mutually exclusive conditions that negate each other;
  hover a redundant negation to see why it can be removed.
- `input input_a; slot a; a <- input_a when not available(a);` reports that there is no
  consistent result whenever `input_a` is present.

Each open file is a separate program. New edits withdraw old findings immediately;
results arrive from the background worker for the current snapshot only. Highlighting,
comment toggling and brackets are configured; completion, navigation, rename and code
actions are not implemented yet.

## Check it

```sh
just test-inputmapping-extension   # package and example checks (no GUI)
just test-inputmapping-vscode      # installed VS Code smoke (needs a local VS Code)
```
