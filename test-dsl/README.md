# InputMapping (test DSL)

InputMapping is the first DSL built on the Denotate IR: a small language mapping inputs
to slots. It exercises the whole path a bespoke DSL takes — parsing, lowering with
provenance, checking, source-linked presentation, its own editor, and export to `.den`.

```text
input kind, first_input, second_input;
slot first, second;
first <- first_input when input_value(kind) is 1 and not available(second);
second <- second_input when input_value(kind) is 2 and not available(first);
```

- Declarations: `input …;` and `slot …;` (separate name spaces; the expected kind
  resolves equal spellings). Mappings: `target <- input [when condition];`. Masks:
  `mask slot [when condition];`.
- Conditions combine `available(slot)`, `present(input)`, `input_value(input) is N` and
  `slot_value(slot) is N` with `and`, `or`, `not` and parentheses. Each input is absent
  or holds one signed 64-bit integer.
- The built-in library defines `present`, `supplies`, `available` and `slot_value`,
  the obligation that at most one input supplies a slot, and the assumption that each
  input has at most one value.

## Pipeline

1. **Parse** (`grammar/`, `src/syntax.rs`) into a source-spanned AST.
2. **Lower** (`lowering::lower`) to a `Corpus` with attribution: user errors
   (name, kind, duplicate, literal) produce diagnostics and no IR; construction or
   attribution failures are creator-facing errors. Conditions go through
   `denotate-normalize` recipes, cached and installed fresh per snapshot.
3. **Check** through `denotate-check-session` (BDD or SAT).
4. **Present** with InputMapping wording on top of `denotate-presentation`: conflicting
   inputs, quoted guards, example observations, related locations, and explicit
   safe-removal eligibility for redundant guards (rewrite warnings).
5. **Export** to `.den` (`src/export.rs`, `just export-inputmapping`): one `.den` file
   per source plus a generated library root, with embedded origins.

## Commands

```sh
just demo-overlap                   # source-linked findings for a built-in example
just parse-inputmapping             # parse and lower a file, no checking
just export-inputmapping OUT FILE…  # export one combined program as .den
just test-inputmapping-lsp          # LSP scenarios against the InputMapping server
cargo +1.93.0 test --manifest-path native/Cargo.toml --locked -p denotate-test-dsl
```

The editor lives in [vscode/](vscode/README.md). The server (`src/server/`) uses the
shared scheduler and server loop from `denotate-editor`; each open file is one program.

## Fixtures

`fixtures/` holds the regression corpus used across the repository and the expected
behavior of each corpus program; see [fixtures/README.md](fixtures/README.md). The
corpus feeds the `.den` round trip and the editor parity test. Regenerate
expectations only for intended behavior changes, and review the diff.
