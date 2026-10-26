# denotate-ir-text

The `.den` format library: parsing, strict loading into a checked program, printing,
embedded origins, folder-root membership and the incremental editor index. The format
itself is described in [docs/den-format.md](../../docs/den-format.md).

It compiles the committed parser generated from `grammars/den` (needs a C compiler, not
Node). Apart from the `filesystem` command adapter it performs no IO: callers supply
program membership and authoritative snapshots.

## Loading

`load(&ProgramMembership, &[SourceFile])` returns a `LoadedProgram`: `Corpus`, semantic
keys, finite domains, exact current `.den` provenance, documents
with their ownership, and occurrence owners. It requires snapshots for every reachable
member, ignores unrelated documents and rejects conflicting snapshots of one URI.

Named assumptions and verifications are declarations in `Corpus`, with typed semantic
keys and occurrence-based provenance (including embedded origins). There is no separate
loader-owned assumption table. `verification_requests(limits)` returns one
`(VerificationKey, CheckRequest)` per verification in the whole reachable closure,
sorted by key; it returns an empty list when no verification is declared. Each request
selects exactly its declaration's assumptions and obligations. References use shared
namespace lookup and resolve only the kind required by their list.

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
takes the corpus, domains, sources, provenance and an explicit `ExportLayout`
(a file for every top-level occurrence, including assumptions and verifications), and returns
named files plus root manifests. Library files go under `library/` with their own
root. `ExportBundle::documents(base_uri)` reloads a bundle in memory.
`PrintOptions { embedded_origins: false }` omits origins.

Assumptions and verifications are printed from IR declarations with ordinary
top-level layout placements and provenance. There is no separate export assumption
record; API callers declare both contracts in the corpus before exporting.

`spelling(name, NameKind)` is the kind-aware spelling used by the printer; editors must
use it for replacement names (rename), not display quoting.

`at_least_one` obligations load and print through the ordinary contract declarations;
`at_least_one` assumptions are rejected. Grouping uses resolved domains, including
explicit overrides. Coverage results and diagnostics are described in the
[format](../../docs/den-format.md#coverage-obligations).

## Editor index

`index::Index` is the recoverable editor boundary. The editor supplies each file's
`SourceFile` and incremental Tree-sitter tree plus explicit membership. The index
shares name decoding, visibility and lookup keys with the strict loader, keeps
per-file projections with current anchors, and resolves per program on demand with
Salsa-tracked queries. Trivia refreshes anchors without invalidating answers; damaged
signatures suppress cascades. It does not need a successfully loaded `Corpus`.

Verification declarations retain their contract kind and projected reference lists.
The index and loader share list resolution, including wrong-kind, ambiguous and
duplicate-reference errors. Typed contract references also drive navigation and validated
rename. Completion uses the same candidates, restricted to assumptions or obligations
by the list being edited, including empty and unfinished lists.

Rule linting comes from `denotate-analysis`.

## Presentation

`presentation::present(&LoadedProgram, &CheckedReport)` adapts the shared presenter
for `.den`: current provenance supplies primaries, upstream origins are related, and
user files are the program's own documents.

## Commands and tests

```sh
just check-den crates/ir-text/fixtures [--verification library::default_checks]
cargo +1.93.0 test --locked -p denotate-ir-text
```

`examples/check.rs` backs `just check-den`. The round trip of the test DSL
regression programs through printing and loading lives in
`crates/test-dsl/tests/ir_text_roundtrip.rs`.
