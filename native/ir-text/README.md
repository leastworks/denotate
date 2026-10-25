# denotate-ir-text

The `.den` format library: parsing, strict loading into a checked program, printing,
embedded origins, folder-root membership and the incremental editor index. The format
itself is described in [docs/den-format.md](../../docs/den-format.md).

It compiles the committed parser generated from `den/grammar` (needs a C compiler, not
Node). Apart from the `filesystem` command adapter it performs no IO: callers supply
program membership and authoritative snapshots.

## Loading

`load(&ProgramMembership, &[SourceFile])` returns a `LoadedProgram`: `Corpus`, semantic
keys, finite domains, active assumptions W, exact current `.den` provenance, documents
with their ownership, and occurrence owners. It requires snapshots for every reachable
member, ignores unrelated documents and rejects conflicting snapshots of one URI.

`load_with_resolver(…, Some(&mut resolver))` also restores embedded origins through a
caller-owned `origins::OriginResolver` (one resolution per URI/view/hash identity).
`&Sources` resolves in-memory snapshots; `filesystem::FileOriginResolver` reads local
files for commands. Upstream origins land in `embedded.provenance`, separate from
current provenance; unavailable or changed sources produce `embedded.notices` and no
fabricated spans.

`ProgramMembership` holds the selected root and `RootInfo { files, libraries }` per
root; `ProgramMembership::single` builds an in-memory one-root program.
`filesystem::discover` resolves `den.root` folders on disk for the CLI.

## Printing

`print(&ExportProgram, PrintOptions) -> Result<ExportBundle, ExportError>` is pure. It
takes the corpus, domains, sources, provenance, assumption records and an explicit
`ExportLayout` (a file for every top-level occurrence and assumption), and returns
named files plus root manifests. Library files go under `library/` with their own
root. `ExportBundle::documents(base_uri)` reloads a bundle in memory.
`PrintOptions { embedded_origins: false }` omits origins.

`spelling(name, NameKind)` is the kind-aware spelling used by the printer; editors must
use it for replacement names (rename), not display quoting.

## Editor index

`index::Index` is the recoverable editor boundary. The editor supplies each file's
`SourceFile` and incremental Tree-sitter tree plus explicit membership. The index
shares name decoding, visibility and lookup keys with the strict loader, keeps
per-file projections with current anchors, and resolves per program on demand with
Salsa-tracked queries. Trivia refreshes anchors without invalidating answers; damaged
signatures suppress cascades. It does not need a successfully loaded `Corpus`.

Rule linting comes from `denotate-analysis`.

## Presentation

`presentation::present(&LoadedProgram, &CheckedReport)` adapts the shared presenter
for `.den`: current provenance supplies primaries, upstream origins are related, and
user files are the program's own documents.

## Commands and tests

```sh
just check-den native/ir-text/fixtures [--sat]
cargo +1.93.0 test --manifest-path native/Cargo.toml --locked -p denotate-ir-text
```

`examples/check.rs` backs `just check-den`. The round trip of the InputMapping
regression programs through printing and loading lives in
`test-dsl/tests/ir_text_roundtrip.rs`.
