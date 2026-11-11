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

Restoration builds a current-document/range index once per load when annotations
are present. It batches each upstream source's requested coordinates into one
forward scan, including within long lines; it stores only requested boundaries.
These indexes belong to the supplied snapshots and are not caches across edits.

To measure loading with an abstract generated program:

```sh
just bench-den-origins 80 100
just bench-den-origins 10 100 1000000 --long-line
```

Arguments are file count, items per file (default 100), upstream source padding
(default 0), and optional `--long-line`. Each item generates an annotated constant,
fact and rule. The release benchmark compares omitted, unavailable and resolved
origins, reports discovery/loading/checking separately, and checks the same proved
outcome at default limits. Generated files are temporary. Timings are measurements,
not test expectations; this is a loader benchmark, not a production scorecard.

`ProgramMembership` holds the selected root and `RootInfo { files, libraries }` per
root; `ProgramMembership::single` builds an in-memory one-root program.
`filesystem::discover` resolves `den.root` folders on disk for the CLI.

Input declarations may name a provider with `within relation`. Loading resolves it
through the shared relation resolver and delegates signature and dependency-cone
validation to `Corpus`. The provider reference participates in navigation, rename
and completion; export prints it from `Relation::input_domain`.

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
use it for replacement names (rename). `presentation::diagnostic_names(corpus)`
provides the same kind-aware spelling and qualified names to the shared presenter.
Generated helper labels share the exporter's allocator, including replacements for
invalid or duplicate API labels. Both frontends use this callback for shared tuple
notes; the test DSL retains its own decoded observation vocabulary.

`at_least_one`, `exactly_one` and `empty` obligations load and print through ordinary
contract declarations and named assumptions. Assumption dependency cones must be
independently stratified; loading and construction requests share IR validation.
`empty(R)` has no grouping argument, and supplying one is a syntax error. Exactly-one
remains one declaration and selection through printing and reloading. Grouping uses
resolved domains, including explicit overrides. Coverage results and diagnostics are described in the
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
just check-den crates/ir-text/fixtures [--verification library::default_checks] [--json] [--verbose]
just check-den <program> --empty-examples all
just check-den <program> --timeout-ms 60000 --max-work 100000000
just check-den <program> --json --no-progress
just check-den --help
just test-crate denotate-ir-text
```

`examples/check.rs` backs `just check-den`. By default it prints shared presented
diagnostics grouped by verification: source URI, one-based line/Unicode-scalar column,
kind, message, notes and labeled related locations. By default only producing rules,
the checked obligation and upstream origins are expanded; other related entries
collapse to "+N more". `--verbose` prints all related locations. `--json` retains the previous
`Results: {...}` status summaries with their existing headers and notices.

Detailed progress goes to **stderr** by default, also with `--json`. It reports
effective limits, source inventory, loading and assumption validation, each selected
verification's declarations, preparation/admission/checking/presentation, prepared
sizes, result counts and session reuse. Every phase starts with a flushed line;
transitions report elapsed time. `--no-progress` disables this checker trace.
`--verbose` remains a diagnostic-layout option, independent of progress.

Fixed facts are shared across verifications, with bounded session reuse across edits.
Residual preparation and admission run once per selected restriction set in a run;
obligation groups, notices and finding identities remain per verification.
Prepared-size output separates fixed present/absent facts, retained original
evidence and the residual executable graph. `just bench-den-fixed ITEMS [VERIFICATIONS]`
compares cold and warm folded runs with ordinary preparation on an abstract workload;
the optional verification count defaults to four. `--two-selections` alternates
restriction sets and `--ground-assumption` includes raw-graph validation. An
input-dependent edit measures fold reuse. Its measurements are not goldens.

The CLI and LSP share `progress::CheckProgress` and `Phase`: identical phase names,
verification metadata and prepared sizes. Delivery remains with each frontend.
Counts describe completed preparation, not an estimate of checking work remaining.
The checking phase includes obligations, notices, replay and session bookkeeping;
it does not yet stream individual queries or live BDD node counts. Progress never
runs an additional check, changes a semantic budget or enters a cache key.

All public `Limits` resource ceilings are configurable for this invocation:
`--max-atoms`, `--max-rules`, `--max-dependencies`, `--max-work`,
`--max-bdd-variables`, `--max-bdd-nodes`, `--max-bdd-tasks`, and
`--max-condition-nodes`, plus `--timeout-ms`. Values are nonnegative integers;
zero allows no use of that resource. `--help` lists the actual default values.
Limits remain per operation/query; the cooperative timeout is not a total command
deadline and does not cover loading or presentation. Exhaustion remains explicit
inconclusive, with the existing exit-code policy. Cache-retention policies and
separate diagnostic attribution allowances are unchanged.

`--empty-examples N` retains a positive number of examples per emptiness obligation
(default three); `--empty-examples all` retains every confirmed tuple, including in
JSON summaries. Counts remain lower bounds if checking is incomplete. It does not
change verdicts or exit-code policy, and it does not enumerate alternative
derivations or worlds for the same tuple.

`--hide-library-rewrites` hides diagnostics for rewritten rules owned by included
libraries, with a count of hidden findings per verification. Own-file rewrites and
all other diagnostics remain visible. The full finding inventory stays in the
status summary, including with `--json`, and exit codes stay unchanged. The shared
view filter is `Presentation::hide_library_rewrites`; it checks rule ownership,
not where a diagnostic happened to be placed.
See the [command contract](../../docs/den-format.md#commands) for ordering and exit codes.

The round trip of the test DSL
regression programs through printing and loading lives in
`crates/test-dsl/tests/ir_text_roundtrip.rs`.

Selected contextual condition notices load and print as ordinary IR declarations:
`notice n: varies(condition, within: scope);` and the optional verification field
`notices: [n];`. Both relations are zero-arity; omitting `within` means the full
permitted context. Origins and the shared editor resolver apply normally. CLI human
output includes advisory diagnostics, including Information when a selected condition
could not be analysed (unsupported dependencies or exhausted limits/deadlines).
JSON also includes quiet notice results. Inconsistent contexts keep only their context
Error; notice findings do not change exit codes.
Notice outcomes do not change exit codes. See the
[format documentation](../../docs/den-format.md#contextual-condition-notices).
