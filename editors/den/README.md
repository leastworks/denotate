# The `.den` editor

A Rust language server ([`crates/den-lsp`](../../crates/den-lsp), crate `denotate-lsp`) and a VS Code extension
(`src/extension.cjs`) for the [`.den` format](../../docs/den-format.md). Language
semantics come from `crates/ir-text`; this package owns the editor: program
discovery, buffers, background checking, publication, navigation and rename.

## Try it

```sh
just edit-den editors/den/examples/semantic-checking
```

Run from the repository root with rustup, Node 22+, just and VS Code's `code`
launcher installed. The command prepares dependencies, builds the extension and
opens the sample. You can also open this editor's source folder in VS Code and use
its F5 launch configurations; their npm build tasks share the scripts used by `just`,
including automatic dependency setup.

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
just edit-den /tmp/example-den
```

Findings on the exported `.den` carry related locations into the `.testdsl`
source; **Denotate: Go to Origin** jumps there (hash-checked; a changed source is
reported, not navigated). Do not commit generated exports: they contain absolute
`file://` URIs.

The [Shipping News tutorial](examples/shipping-news/README.md) builds a complete
message-mapping and classification example in nine runnable steps; lesson 10 adds
computed values that feed task conditions.

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

Set **Denotate: Show Library Rewrites** (`denotate.showLibraryRewrites`) to `false`
to hide consumer-program rewrite warnings about included library rules. The default
is `true`. The library's own program still shows its warnings, and errors and other
findings remain visible everywhere. Full per-verification status inventories remain
available; the status tooltip shows how many rewrite findings were hidden. Changing
the setting refreshes publication without requiring a source edit.

## Progress and output

While background checking runs, the status bar shows a spinner and a count such as
**Denotate: Checking 3/8 programs**. Hover to see the active program and how many
programs are queued, checked, blocked, without verifications, or interrupted.
The count includes library home programs; “processed” does not mean “proved”.
Editing a program can put it back in the queue, and adding roots changes the total.
For a single large program, the item shows the active phase and verification, such
as **Admission · verification 2/3**. After preparation, its tooltip includes inputs,
ground atoms, rule instances, components and largest component size. The clock
shows time since the last server report; it is not a heartbeat or time remaining.
Startup and discovery show an indeterminate spinner. When idle, the item resumes
the active `.den` file's status.

During admission the status item also shows the round and unresolved-component
count. The tooltip and Output identify the current stage and reported component,
its representative ground tuple and current `.den` source location, its size,
and committed rewrite counts. Upper-bound component starts are reported before
analysis; ordinary scan/iteration updates are throttled. Exhaustion forces a
report of the precise current work and resource. Reused admission is labeled.
Counts describe components containing negation cycles, not every possible cycle;
blocked atoms include downstream dependents. Components may split between rounds,
so these counts are not a monotonically decreasing percentage.

“Evaluating fixed facts” runs once per program check, shared across its
verifications. A completed keyed fold is retained across runs without a byte cap;
its accounted bytes appear in the tooltip and Output separately from bound evidence
sizes. Other cache allowances are unchanged. The tooltip and Output separate fixed
present/absent facts, retained
original evidence and the residual executable graph. A small residual does not mean
the retained evidence has disappeared; these counts are not memory measurements.

Phase updates also show process RSS and, on macOS, physical footprint in the
tooltip and Output. Values are bytes; peaks are process lifetime high waters,
including other checked programs and caches. Unsupported readings are `null`.
For a detailed profile through admission, use `just check-den <program>
--profile-memory <new-file.jsonl>`; see
[memory profiling](../../docs/checker-policies.md#memory-profiling).

Click the status item or run **Denotate: Show Output** to open **Output → Denotate**.
This is the normal log view: startup, phase transitions, prepared sizes, completion
summaries, and operational errors such as a failed check or deadline. Run numbers
identify replacements after edits: the same run staying in one phase differs from
new runs repeatedly starting. Select **Debug** using the output
channel's log-level control for detailed count and active-program updates. Routine
progress does not open the panel automatically. Source diagnostics remain in
**Problems**. The **Debug Console** is useful when developing the extension with
F5; users do not need a debugging session to see Denotate's logs.

Library findings can appear before a consumer finishes: the library has its own
home program, and structural/configuration diagnostics can precede semantic checks.
The timeout is applied to checking operations, not to the workspace as a whole;
multiple verifications and queries can take longer in total. If CPU stays high
without edits, the last phase, run number and size report help identify where work
remains. A phase that stays unchanged does not by itself prove the process is stuck.

## Checker limits

Set `denotate.timeoutMs` and `denotate.limits` in user or workspace settings. One
configuration applies to every program in the VS Code window, including library
programs. For example:

```json
{
  "denotate.timeoutMs": 60000,
  "denotate.limits": {
    "maxAtoms": 200000,
    "maxBddVariables": 30000
  }
}
```

These are example overrides, not recommended defaults. `limits` accepts `maxAtoms`,
`maxRules`, `maxDependencies`, `maxWork`, `maxBddVariables`, `maxBddNodes`,
`maxBddTasks` and `maxConditionNodes`, matching the CLI controls. Omitted fields use
checker defaults; zero allows no use. Limits apply per operation/query, and timeout
is cooperative. Loading and presentation are outside that allowance. A limit change
cancels obsolete checking and automatically rechecks all affected programs.
Invalid settings are reported in Output and retain the last valid configuration
(defaults at startup). Removing an override restores its default.

Output logs the effective values at the start of each check and explains resource
exhaustion, including its subphase, effective ceiling and observed demand when known.
For example, reaching the atom limit while grounding an input-domain provider is
distinct from reaching it while enumerating eligible inputs. Observed demand can
include a rejected addition; it is not the eventual total size. Unknown solver
counts are omitted. Internal capacity and remaining work/storage may impose a tighter
ceiling than the configured value. Inconclusive results remain inconclusive.

## Tests

```sh
just test-den          # server component tests, syntax manifest, all shared LSP scenarios
just test-den-origins   # Go to Origin unit tests
just test-den-progress # progress labels and logging tests, no editor
just test-den-vscode   # installed VS Code smoke (needs a local VS Code)
```

`just build-den` prepares pinned dependencies, checks the parser from `grammars/den`, builds the release server
and bundles the extension into `dist/`. Parser generation uses a local content
fingerprint in `target/den-parser-generation.json`: the grammar, tree-sitter
configuration, pinned generator executable/version, Node version and generation
script. It also checks the generated files' contents; missing or modified outputs
trigger regeneration. The grammar is self-contained; any future imported helper
must be added to the script's input list.

Generation runs in a temporary directory and copies back only changed files, so
identical output keeps its timestamps and does not invalidate Cargo's parser build.
A missing cache is harmless. Failed generation preserves the old outputs and cache.
`just generate-den --force` bypasses the cache; CI uses this before checking that
the committed parser is current. `just test-den-generation` tests these behaviors
with isolated grammars and the pinned generator.

`just edit-den <folder>` uses this same build. With unchanged inputs, parser generation
is skipped and Cargo reuses the server; extension bundling and copying still run.

Dependency setup is automatic for editor build, generation and test recipes. A
local stamp inside `node_modules/` records the package/lockfile contents and runtime;
changes or missing required tools trigger a fresh install. `just setup-den --force`
explicitly reinstalls dependencies. Parser generation has its own cache described
above, so dependency setup does not force unchanged generated files to be rewritten.
