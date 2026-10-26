# `.den` editor protocol

The `.den` server speaks standard LSP plus the custom methods below. The VS Code
extension implements the client side; headless clients can use the same contract.

## Programs and home ownership

Program membership follows the [`.den` format](../../docs/den-format.md#programs-denroot).
The server discovers workspace roots and referenced external libraries, canonicalizes
identities and keeps cycle-safe edges. Open documents outside the workspace discover
their nearest root. There is no implicit workspace-folder root.

Each file has one **home program**: the root that owns it directly (nearest manifest),
or itself as a standalone program when no root contains it. Every known root, including
library-alone programs and roots with no own files, is a separate program. Nothing is
selected, preferred or merged.

A malformed manifest keeps its last known-good library links. Missing dependencies
keep their identities and watcher subscriptions. Unreadable or out-of-sync members
block only the programs that contain them; broken discovery never turns a file into
a standalone program. Syntax damage blocks checking but keeps reliable completion
and navigation. Ordinary `.den` edits do not rescan folders.

### Requests

- `denotate/roots {uri}` returns
  `{uri, homeProgram, state, errors, checking, backend, verifications, uncheckedObligations, findings, summary?, originNotices?, checkRevision?}`.
  `state` is `standalone`, `ready` or `invalid` and describes resolution readiness,
  not a successful check. `homeProgram` is a canonical manifest URI (null when
  standalone or unresolved).
- `denotate/roots {}` returns `{programs: [{program, state, errors, checking, …}]}` for
  every known program and standalone document.
- `textDocument/codeAction` offers **Create den.root here** and **Create den.root in
  another folder…** for standalone documents. The extension command
  `denotate.createRoot [documentUri, folderUri?, chooseFolder=false]` creates `{}`
  exclusively (never overwriting an existing or open manifest) and triggers discovery.

The status bar shows the home program, verification count and aggregate outcome.
Its tooltip includes one line per verification with its assumptions, mode, consistency,
checking state and outcome, plus unchecked obligations and origin notices.

## Findings and publication

A program's findings are published on its **own** files. Primary locations are
participating occurrences in those files; library occurrences and upstream DSL origins
are related locations. If a finding involves none of the program's own files, it is
published on the library location labeled `in <program>: …` (workspace-relative
where possible) and listed in that program's status. This labeled fallback is the only
cross-program publication and is never deduplicated across programs.

A consumer-caused library failure (for example, a consumer declaration that makes a
library name ambiguous) is reported in the consumer's status and on the conflicting
consumer declaration, with the library location related.

`checking` is `pending`, `checking`, `complete`, `unconfigured`, `blocked`,
`deadline`, `cancelled` or `failed`. `unconfigured` means the complete program has no
verification declarations: it publishes no admission, obligation, no-meaning,
unsupported-region or rewrite findings. Syntax, resolution, type and structural
checks remain available. Invalid verification syntax or references block checking;
they never trigger an implicit verification.

`verifications` is null while configuration cannot be resolved, otherwise a list in
verification-key order:

```json
{
  "verification": "library::default_checks",
  "assumptions": ["library::one_present_input"],
  "mode": "normal",
  "consistency": "consistent",
  "checking": "complete",
  "summary": {"state": "proved"}
}
```

Names are qualified `.den` spellings (`::checks` for a global name). `mode` is
`normal` or `consistency-only`; the latter selects no obligations but still runs
context-wide semantic analysis. `consistency: "consistent"` follows from the
all-absent input world permitted by every currently supported assumption; it is
not an admission or obligation proof. `summary` is null until that verification has
a current result, then contains the shared checker summary (backend, lowered input
restrictions, groups, regions, incomplete work and finding inventory).
`complete` means execution finished, including conclusive findings or explicitly
inconclusive scopes; `summary.state` is `proved`, `findings` or `incomplete`.
Operational deadlines/failures are recorded on the affected verification; independent
verifications still run. Cancellation withdraws the obsolete program job.

The program-level `summary` contains `state`, `checking`, `verifications`,
`uncheckedObligations`, `findings` and `originNotices`. Its state is `unconfigured`
with no verifications; otherwise any unchecked obligation, unfinished verification
or incomplete summary makes it `incomplete`. With all work complete it is `findings`
if any verification has findings, otherwise `proved`. Known findings remain listed
even when the aggregate is incomplete. Proved obligations appear only in summaries.
`originNotices` reports unavailable or changed sources separately from findings.

`uncheckedObligations` is null for unresolved configuration, otherwise a sorted list
of qualified obligation names selected by no verification in the program's closure.
Selections are independent of execution: pending, blocked or inconclusive selected
checks are never reported as unchecked. Notices are computed before checking and
remain available while checks are pending or exhausted. Each unchecked obligation
gets one Information diagnostic per program at its declaration, including the labeled
library fallback: `Obligation <name> is not checked by any verification in program
<program>.` The code is `unchecked-obligation`; its data uses the program/obligation
identity (`finding.uncheckedObligation`), not a semantic verification identity.

An explicit empty obligation list gets one structural Warning per declaration, in
its own document, even with multiple consumers: `No obligations selected; this is a
consistency-only verification.` Its code is `consistency-only`. It carries no
per-program semantic finding identity.

Each semantic diagnostic's `data` holds `program`, `finding` (an object containing `verification: [namespaceKey, name]` alongside
either a `group`, `region` or `rewrite` identity, or an `obligation`/`component` coverage identity, all built from semantic
keys, never arena IDs or message text),
`kind`, `fallback`, `evidence`, `checkRevision` and `locations` (URI, view, SHA-256
and byte range for primary and related spans). Counterexamples may produce several
highlights with one finding identity. Publication identity is the full
`(data.program, data.finding)` pair: two verifications of the same obligation remain
distinct even with identical assumptions. Messages do not embed context labels;
unsupported and inconclusive findings use one
primary with the other producers related. Evidence kinds are
`replayed-counterexample`, `replayed-coverage-counterexamples`, `no-meaning-observation`, `unfounded-support-world`
(never an overlap witness), `rewrite-proof` and `no-witness`. Rewrite proofs do not
authorize edits.

### Coverage results

A coverage finding uses
`{"verification": [namespaceKey, name], "obligation": [namespaceKey, name], "component": "coverage"}`.
Program ownership remains `data.program`. Its identity is independent of displayed groups
and witnesses. Coverage failures have one primary diagnostic per obligation/verification;
uniqueness retains its existing per-overlap-group reporting and identities.

`summary.coverage` (present when coverage is selected) lists entries with `identity`,
`outcome` (`proved`, `counterexample`, `unsupported`, `inconclusive`), `examinedGroups`,
`missingGroups: {count, exact}`, `complete`, `noGroups`, `unsupportedGroups` and `reason`
(null or `{phase, resource}`). The count is of distinct groups with an established
failure in at least one permitted world. An incomplete count is a lower bound.
A failure can coexist with `complete: false`; it remains a failure and blocks a proof.

Coverage counterexample evidence has kind `replayed-coverage-counterexamples`, component
`coverage`, the same `missingGroups`, `complete`, `unsupportedGroups` and `reason`, and
`examples` (currently at most three, ordered by semantic group keys). Each example contains
`group` (typed constant keys), its own `observation: {present, absent}`, and replay `scope`
(`whole-program` or `cone-only`). Examples need not share an input world. Limiting the
sample does not make an otherwise completed check incomplete. Other coverage outcomes
carry `no-witness` evidence.

An empty resolved grouping-column domain gives a proved coverage result and an Information
diagnostic with code `empty-grouping-domain` at the obligation: `no groups: the grouping
domain is empty`. This note does not invalidate the proof. `group_by: ()` always creates
one global group and never gets this note. Normal unselected-obligation notices and
consistency-only handling also apply unchanged.

### Configuration

`initializationOptions.denotate` or
`workspace/didChangeConfiguration {settings: {denotate: {backend, timeoutMs}}}`:
`backend` is `bdd` (default) or `sat`; `timeoutMs` defaults to 10000 and bounds each verification's check separately, so a
program with several verifications may take that long per verification. An update
replaces the whole object. The VS Code setting is `denotate.backend`.

### Scheduling

Every verification in the reachable closure runs once in each including program,
using that program's facts and domains; consumers may add verifications over library
declarations. Each program has one session and one job that executes its verifications
in key order, checks cancellation between contexts and publishes the merged results
atomically. No verification is implicitly selected when none exists.

At most one job runs and one latest job waits per program; a queued replacement keeps
its FIFO position, while a replacement for the running program joins the tail. Member,
manifest, dependency, home, origin or configuration changes withdraw the old findings
and cancel obsolete work; syntax feedback remains. A temporarily uncheckable program
is blocked but keeps its warm session; only removing the program releases it. Before
publishing, the server compares the complete current observation again and validates
every destination; a job that finished before cancellation can still be discarded.

## Manifests and watchers

The extension sends `denotate/manifest {uri, text, version}` for every open `den.root`
(any language ID) initially and on open, change and save; `version` increases
monotonically and stale versions are ignored. `{uri, closed: true}` drops the
override and reloads disk. Standard `textDocument/*` notifications for `den.root` are
ignored, so a manifest is never parsed as `.den`.

Clients that set `initializationOptions.originSnapshotBridge: true` receive
`denotate/rootsChanged {watchFolders}` and maintain non-overlapping watchers for
`**/{*.den,den.root}` in workspace and referenced folders (an existing ancestor if a
library folder is missing), forwarding `workspace/didChangeWatchedFiles`. Other clients
can use standard dynamic registration. Disk events never replace open snapshots, even
when watcher and editor URIs spell a canonical path differently.

## Origin snapshots

Bridge clients receive `denotate/originSubscriptions {uris}` for source URIs found in
indexed source-location declarations, watch them, and observe open, change, save and
close events in **all** languages, sending `denotate/originChanged {uri, generation}`.

The server requests `denotate/originSnapshot {uri}` only for known origins. Responses:

```
{uri, text, open, dirty, generation, version?, bufferUri?, bom?}
{uri, unavailable: "reason"}
```

The client checks every open document first, including canonical aliases; only when
none is open may it read disk. A read that races a newer observation returns
unavailable. The server accepts only the latest request per URI, computes SHA-256
itself and checks the requested content hash before using a snapshot. Dirty state
alone is not a mismatch. A failed request never permits a server-side disk fallback.

**BOM.** VS Code reports UTF-8-with-BOM buffers as `encoding: "utf8bom"` and omits the
signature from `getText()`. The client restores exactly one U+FEFF and sets
`bom: true`. Hashes and byte spans always include the signature; displayed ranges
subtract one column on the first line (and Go to Origin one UTF-16 unit).

`denotate/originStatus {uri}` reports `unknown`, `unavailable`, `matching` or
`hash-mismatch` with the current and expected hashes.

## Go to Origin

`denotate/origins {textDocument: {uri, version?}, position}` returns
`{version, origins: [{uri, view, hash, start: {line, column}, end: {line, column}}]}`.
Coordinates use the `.den` format's one-based Unicode scalar columns and LF-only
lines (not LSP ranges). The smallest annotated occurrence containing the cursor (or
ending at it) wins. Distinct views, hashes and ranges stay separate; library sources
are never filtered. Out-of-sync documents, version mismatches and unloadable programs
are errors.

**Denotate: Go to Origin** opens a single available origin directly and otherwise
shows a picker (URI, view, range, hash), including unavailable ones with the reason.
After the picker it resolves the source again, verifies hash and coordinates on that
exact text and on the opened document, and refuses if the `.den` document changed
meanwhile. Missing, changed or invalid origins produce a notice, not a jump.

## Verification language services

Assumption, obligation and verification declarations participate in definition,
references, hover and document outline. Selection-list references use the same typed,
program-scoped resolver as loading: `assumptions` offers only assumptions and
`obligations` only obligations, including while lists are incomplete. Ambiguous names
are offered with namespace qualification. Names of different contract kinds remain
independent even when spelled alike.

Contract names use the standard `event` semantic token type (appended to the existing
legend); the outline and completion also use `Event`. Formatting indents verification blocks and
preserves comments, quoted names and attached origins.

## Rename

`textDocument/prepareRename` and `textDocument/rename` cover sorts, relations, typed
constants, rule-local variables, namespace segments (the segment under the cursor),
relation parameters and their `group_by` references, assumption/obligation names and
their verification-list references, verification names, and file-local aliases.
`newName` is the logical name: replacement text comes from the printer's
`spelling(name, NameKind)` (a constant `I` becomes `'I'`, a variable `?'lower case'`).
Generated helpers keep `$`, aliases `#`. Prepare returns `{range, placeholder}` when
the decoded name differs from the source token.

Edits are collected in **every affected program**, including unopened consumers of a
shared library. Broken discovery, malformed manifests, syntax errors or out-of-sync
members in an affected program block the rename. A dry run on fresh indexes requires
every edited and untouched reference to resolve to the corresponding declaration, and
rejects capture, new ambiguity, namespace merges, unresolved references and new
duplicate, type or structural errors. Before returning versioned `documentChanges`
(null versions for closed files), the server checks the observation again. Workspace,
read-only, generated-folder and dependency protections apply to every edited file.

## Test mode

With `DENOTATE_TEST_MODE=1` the server exposes the shared checking test protocol
(`crates/editor` README): `denotate/test/checkingIdle`, `hold` (`beforeResult` or
`duringCheck`), `checkpoint`, `release`, `resetChecks`, `checkingStats` and `checked`.
The `.den` server's checking-idle barrier also waits for pending origin replies; its
ticket identity is `{program, revision}`. `denotate/test/idle` and `validated` remain
fast editor barriers and do not imply that checking finished.
