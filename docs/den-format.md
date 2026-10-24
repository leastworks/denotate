# The `.den` format

`.den` is the text form of the Denotate IR. It is both an authoring format and an
export format: a DSL can print its lowered program as `.den`, with embedded origins
pointing back to the DSL source. The grammar is `den/grammar/grammar.js`; the loader
and printer are in `native/ir-text`.

## A small program

```den
namespace demo;
sort S;
const a, b: S;
input value(x: S);
relation present(x: S);
present(X) :- value(X);
assumption unique_input: at_most_one(value, group_by: ());
obligation unique_output: at_most_one(present, group_by: ())
    message "At most one value.";
domain S = [a, b];
```

- **Sorts and constants.** A sort's domain defaults to all its declared constants in
  the program (none means empty). One `domain Sort = [...]` may override it.
  Constants used by rules must belong to the domain.
- **Relations** are `input` (supplied by the environment) or derived (`relation`).
  Inputs cannot be defined by rules.
- **Rules** are `head :- body` with positive and `!`negated atoms; facts have no body.
  Variables are uppercase identifiers or `?'any name'`; `_` in a positive body is a
  fresh variable. Integers are typed constants (`01` canonicalizes to `1`).
- **Contracts.** `obligation name: at_most_one(rel, group_by: (cols))` is checked.
  `assumption` constrains input worlds (W); every assumption in a program is active.
  Only input `at_most_one` assumptions are supported.
- **Names.** Quote any non-identifier or reserved word: `'007'`, `'module'`.
  Escapes: `\\`, `\'`, `\n`, `\r`, `\t`. Parameter names and `group_by` columns accept
  reserved words unquoted. `$condition_N` is a generated helper (zero-arity, derived),
  distinct from a frontend relation spelled `'$condition_N'`.

## Namespaces

- `namespace a::b;` applies to the rest of the file; `namespace a::b { ... }` blocks
  allow several namespaces per file and nest. Namespaces can span files. Top-level
  declarations without a namespace are global. `module a;` is a deprecated alias of
  the file-scoped form. Only `use` lines and comments may precede a file-scoped header.
- Segments are decoded names: `'a::b'` is one segment, `a::b` two.
- `use a::b;` opens names for its file or block. It loads nothing, is not transitive
  and does not open nested namespaces. Code also sees enclosing namespaces.
- Qualified references always start from the global namespace; `::name` selects a
  global declaration. An unqualified name visible from several namespaces is an
  error (inner names do not shadow outer ones).
- All declarations are installed before rules, so files in one namespace can refer to
  each other without `use`. Duplicates are rejected across the whole namespace.

## Programs: `den.root`

A program is defined by a `den.root` JSON manifest:

```json
{"libraries": ["../common/den.root"]}
```

`{}` means no libraries. A root contains every `.den` file under its folder, stopping
at nested roots. Library roots are included transitively; diamonds and cycles are
visited once. The root's own files are user-owned; reachable library files are
library-owned. There is no implicit root: a `.den` file outside every `den.root` is a
standalone one-file program. Membership never depends on `use`.

## Embedded origins

Origins use MLIR-style locations. Source entries and aliases are file-local and may
be forward-referenced:

```den
p() loc(#positions);
#src = source("file:///example.dsl", view: "dsl", hash: "sha256:ba7816bf…");
#positions = loc(#src { self: 1:1 to 1:4, head: 1:2 to 1:3 });
```

- Coordinates are one-based lines and **Unicode scalar** columns; ranges are
  half-open. Only LF advances a line; CR, BOM and non-BMP characters each count as one
  scalar. A source is identified by URI, view and the SHA-256 of its exact bytes
  (no newline or Unicode normalization).
- Scalar form `loc(#src 1:1 to 1:4)`; several origins `loc(fused[#a 1:1 to 1:2, #b 2:1 to 2:3])`.
  Occurrence maps assign origins per position: `self`, `head`, `head.N`, `body.N`,
  `body.N.M` (zero-based), and `decl.N` for grouped constants. Compact maps
  (`loc(#src { … })`) are equivalent when one source covers every position.
- Undefined, cyclic, duplicate or wrong-kind aliases, malformed hashes and nonexistent
  positions are load errors, including in unused aliases. If a source is missing or
  changed, the loader reports a notice per source and checking continues over the
  current `.den` text.

Every loaded program also has **current `.den` provenance**: every declaration, rule,
atom and term maps to its exact span in the current text, whether or not origins
are embedded. Upstream origins are kept in a separate table.

## Identity

Semantic keys use namespace-qualified declaration identities, never files or source
positions. Rule keys use the rule's namespace, its resolved structure and a duplicate
ordinal. Comments, whitespace, location syntax, moving a declaration between files in
one namespace, and switching between qualified and unqualified spellings of the same
reference do not change keys. Rule order is preserved within a file; cross-file
interleaving is not part of a program's meaning.

## Printing

`ir-text::print` writes an API-built program as `.den` given an explicit file layout.
Names print bare when legal for their kind (constant `i`, variable `I`, integer `1`)
and are qualified only where lookup from the owning namespace would be ambiguous.
Library files go under `library/` with their own root. Output without embedded
origins still reloads with full current-text provenance.

## Commands

```sh
just check-den <folder-or-den.root> [--sat]          # load and check a program
just export-inputmapping <out-dir> <file.inputmapping>…   # export a DSL program as .den
```
