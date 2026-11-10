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

### Checking progress and logs

Clients opting in with `initializationOptions.checkingProgress: true` receive
`denotate/checkingProgress` notifications. Each is a complete, deduplicated snapshot
of current program work, emitted by the owner loop after edits, completions and
starting the next job, before answering checking-idle barriers:

```json
{
  "total": 4,
  "processed": 2,
  "counts": {
    "pending": 1, "checking": 1, "complete": 1, "blocked": 1,
    "unconfigured": 0, "deadline": 0, "failed": 0, "cancelled": 0
  },
  "active": [{
    "program": "file:///app/den.root", "label": "app/den.root", "revision": 12,
    "detail": {
      "phase": "admission", "elapsedMs": 250,
      "verification": "::checks", "verificationIndex": 1, "verificationTotal": 2,
      "assumptions": 1, "obligations": 4, "notices": 2,
      "ground": {"inputAtoms": 50, "atoms": 200, "ruleInstances": 160,
        "components": 60, "largestComponentAtoms": 12}
    }
  }],
  "awaitingSnapshots": false
}
```

`total` includes library home programs and standalone documents. `processed` is
`total - pending - checking`: blocked, unconfigured and interrupted programs count
as processed, not as proved. `complete` means checking finished, regardless of its
semantic outcome; results remain in the ordinary per-verification summaries.
An edit can move a processed program back to pending, and discovery/removal can
change the total. These are current counts, not a monotonic percentage or an estimate
of remaining time. An obsolete running ticket is excluded once superseded. No worker
can publish progress directly or advance it with a discarded result.

`active` lists current checking tickets (at most one with the serial scheduler).
`awaitingSnapshots` indicates the origin bridge still needs current source snapshots.
`detail` is null until the worker reports its phase. Phases are `loading`,
`assumption-validation`, `preparation`, `admission`, `checking`, `presentation`
and `publication`. Loading includes `files`; verification phases include its name,
one-based index, total, and selected declaration counts. `ground`, when available,
is the size after preparation, before admission rewrites, retained through that
verification's checking/presentation. `elapsedMs` is elapsed worker time at the
report, not a deadline or heartbeat. Checking includes obligations, notices, replay
and session bookkeeping; no inner query fraction or BDD node counter is reported.
Skipped phases need not appear. Startup and discovery remain indeterminate.
The phase vocabulary, verification metadata and prepared-size inspection are
shared with `check-den` through `denotate_ir_text::progress`. The CLI additionally
reports its filesystem discovery phase; the editor retains its snapshot-driven
discovery and publication policy.

Updates carry the job's ticket through the shared scheduler, and the owner drops
updates for superseded tickets. A progress-only owner turn does not rebuild source
snapshots. The client renders active progress without requesting program status;
its local clock displays time since the last report without polling the server.

The VS Code status item shows a spinner and counts while work is pending, including
when a different language's editor is active. Its tooltip identifies the active
program and the terminal categories. Once idle, it resumes the active `.den`
document's existing status, or hides if there is none. Clicking the item or running
**Denotate: Show Output** opens the `Denotate` log output channel.

The client logs startup, phase transitions with run revisions and prepared sizes,
and completion summaries at Info, aggregate counts at Debug, and server
stops/operational failures at Warning or Error. Accepted failed
or deadline results also send standard `window/logMessage` warnings, including
available failure details. Stale results do not log an accepted failure. Ordinary
source diagnostics stay in Problems; progress adds no checking work or semantic
results. The Debug Console remains a development/debugging surface.

## Findings and publication

A program's findings are published on its **own** files. Primary locations are
participating occurrences in those files; library occurrences and upstream DSL origins
are related locations. If a finding involves none of the program's own files, it is
published on the library location labeled `in <program>: …` (workspace-relative
where possible) and listed in that program's status. This labeled fallback is the only
cross-program publication and is never deduplicated across programs.

The optional `denotate.showLibraryRewrites` setting (default `true`) controls only
rewrite diagnostic visibility. Supply it under `initializationOptions.denotate` or
`workspace/didChangeConfiguration.params.settings.denotate`. When false, a program
hides diagnostics whose rewritten rule is owned by its library closure. This uses
rule ownership rather than primary location; unknown ownership is kept visible.
Own-file rewrites, the library's home-program diagnostics and every other finding
kind are unchanged. No proofs are merged across programs or verifications.

The full finding inventory and outcomes remain in each verification's summary.
With filtering enabled, `summary.hiddenLibraryRewrites` counts distinct hidden
rewrite findings (not locations). The status tooltip displays that count. Setting
changes participate in snapshot validation and refresh publication; stale diagnostics
are withdrawn. `check-den --hide-library-rewrites` uses the same view filter and
retains its existing exit-code policy.

A consumer-caused library failure (for example, a consumer declaration that makes a
library name ambiguous) is reported in the consumer's status and on the conflicting
consumer declaration, with the library location related.

`checking` is `pending`, `checking`, `complete`, `unconfigured`, `blocked`,
`deadline`, `cancelled` or `failed`. `unconfigured` means the complete program has no
verification declarations: it publishes no admission, obligation, no-meaning,
unsupported-region, rewrite or condition-notice findings. Syntax, resolution, type and structural
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
`normal` (selects obligations), `notices-only` (selects notices but no obligations),
or `consistency-only` (selects neither). All run context-wide semantic analysis. `consistency` is `unknown`, `consistent` or
`inconsistent`. General selections stay unknown until W is computed; input-only
at-most-one selections are known consistent even before checking. A consistent
context is not an admission or obligation proof. `summary` is null until that verification has
a current result, then contains the shared checker summary (backend, lowered input
restrictions, groups, regions, incomplete work and finding inventory).
`complete` means execution finished, including conclusive findings or explicitly
inconclusive scopes; `summary.state` is `proved`, `findings`, `incomplete` or `inconsistent-assumptions`.
The shared summary includes `consistency`; exhaustion before a report leaves a
general selection unknown (input-only at-most-one selections remain known consistent). An inconsistent context contributes findings to the program aggregate,
checks no obligations, and does not prevent other verifications from running.
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
either a `group`, `region` or `rewrite` identity, or an `obligation`/`component` coverage or emptiness identity, all built from semantic
keys, never arena IDs or message text),
`kind`, `fallback`, `evidence`, `checkRevision` and `locations` (URI, view, SHA-256
and byte range for primary and related spans). Counterexamples may produce several
highlights with one finding identity. Publication identity is the full
`(data.program, data.finding)` pair: two verifications of the same obligation remain
distinct even with identical assumptions. Messages do not embed context labels;
unsupported and inconclusive findings use one
primary with the other producers related. Evidence kinds are
`replayed-counterexample`, `replayed-coverage-counterexamples`, `no-meaning-observation`, `rewrite-proof` and `no-witness`. Rewrite proofs do not
authorize edits.

### Ground dependency cycles

Region diagnostics (`unsupported-region`, `no-meaning`, and region-level
`inconclusive`) include a human-readable ground-cycle note with concrete arguments.
`->` means a positive dependency from consumer to provider; `-not->` means a
negative dependency. It shows the checker's retained ordered path, including its
closing edge. It does not enumerate other cycles or imply an execution order.

Their existing `data.evidence` gains `cycles`, using the same shape as assumption
validation: an array of cycles, each an ordered array of edges with keyed `consumer`
and `provider` atoms and `polarity` (`positive` or `negative`). A region carries one
retained cycle. The evidence kind stays `no-meaning-observation` or `no-witness`;
the no-meaning observation and producer fields remain intact. The cycle is structural
evidence, not a witnessed trace or a minimal inconsistent subset. Finding identities,
placement, severity, verdicts and status summaries are unchanged.

Invalid-assumption diagnostics render their existing `cycles` evidence as the same
notes, rebinding semantic keys to the current snapshot's canonical `.den` names.
Both CLI human output and editor messages use the shared presenter. Notice diagnostics
continue to identify blocking rules through related locations.

### Ownership-frontier placement

For library-declared emptiness and uniqueness counterexamples, primaries are the
first locatable consumer producers on each positive branch of each retained tuple's
proof. Facts count as producers; unlocated generated rules are traversed. Relation
and constant declarations, premise occurrences and negative premises never stop the
walk. All participating occurrences remain available as related locations with
their existing labels, including support below the frontier and upstream origins.

Union frontiers across tuples and merge shared locations. A tuple without a locatable
consumer producer keeps its old placement and labeled library fallback independently
of the other tuples. Ownership uses the checked program's own files versus its
entire library closure, not namespaces. Current provenance must establish library
ownership; own-file or unlocated obligations retain existing placement.

No evidence, identity, count, completeness or attribution-status fields change.
Coverage, unsupported/inconclusive findings and no-meaning placement are unchanged.

Human-readable tuples and missing-group arguments use canonical `.den` name
spelling, including qualified namespaces, quoted uppercase constants, reserved
words and escapes. Generated `$helper` names remain distinct from authored
`'$helper'` names. Structured keys and finding identities are unchanged.

### Assumption context diagnostics

General `activeAssumptions` entries retain the existing `relation` and `groupBy`
fields and use kind `at-most-one`, `at-least-one`, `exactly-one` or `empty` (empty
has `groupBy: []`). Semantic keys are unchanged.

An inconsistent context produces an Error with code/evidence kind
`inconsistent-assumptions`, finding identity
`{"verification": [namespaceKey, name], "context": "inconsistent-assumptions"}`.
Its selecting verification is primary and selected assumption declarations are
related; ordinary labeled library fallback applies. No unsatisfiable core is claimed.

Assumption declaration validity is reported once per program, before verifications,
including unselected declarations and programs without a verification. `invalid-assumption`
is an Error on the assumption; `unvalidated-assumption` is Information when grounding
or validation exhausts. Both use finding identity
`{"verification": null, "assumption": [namespaceKey, name], "check": "ground-cone"}`.
Evidence kind is `assumption-validation`, with state `invalid` or `inconclusive`.
Invalid evidence contains `cycles`: arrays of edges with keyed `consumer`, `provider`
atoms and `polarity` (`positive` or `negative`). Cycle rules and premise occurrences
are related locations labeled `blocking dependency cycle`; normal library fallback
and upstream-origin placement apply. Inconclusive evidence names `phase` and `resource`.

The program summary's `assumptionValidation` contains a state (`valid`, `invalid`,
`inconclusive`), an `assumptions` array of keyed declarations with `validation`
evidence, and its finding inventory. A verification selecting an invalid or
unvalidated assumption has an `incomplete` summary, unknown consistency, and
`assumptionValidation` evidence explaining why it was not checked. Other
verifications still run. Any invalid or unvalidated declaration keeps the program
summary `incomplete`, even without verifications; diagnostics remain program-scoped.

A directional `assumed-conclusion` Warning uses identity
`{"verification": [...], "assumption": [...], "obligation": [...], "notice": "assumed-conclusion"}`.
It is primary on the selecting verification, with both declarations related. It
warns only when the assumption relation is or depends on the checked relation,
not when the obligation depends on an assumed premise or merely shares an input.
Evidence kind is `assumed-conclusion`; it is not a witness or a failed obligation.

### Contextual condition notices

Selected `notice n: varies(condition, within: scope)` declarations produce advisory
findings: `impossible-condition` (Warning), `always-true-condition` (Information), or
`unanalysed-condition` (Information).
Their `data.finding` is `{ "verification": [namespace, name], "notice": [namespace, name] }`.
Distinct uses and verifications remain distinct even when their condition is shared.
Each finding has one primary at the notice declaration; `condition being inspected`
and `complete enclosing scope` label related declarations. Unsupported notices also
include the checker-retained cycle rules as `blocking dependency cycle` related
locations. Upstream origins, home-program publication and labeled library fallback
work normally. These notices do not alter `summary.state`, obligation
completeness, or program aggregate results.

When notices are selected, `summary.notices` contains entries in notice-key order:

```json
{
  "identity": {"notice": ["demo", "inner"]},
  "result": {
    "kind": "condition-variability",
    "state": "always-true",
    "reason": null,
    "whenTrue": {"observation": {"present": [], "absent": []}, "scope": "whole-program"},
    "whenFalse": null
  }
}
```

`result` supplies the diagnostic's `data.evidence`, with the additional unknown-cause
details below. States are `impossible`, `always-true`, `varying`, `parent-unreachable`,
and `unknown`. The two examples are
full keyed input observations: each independently replays the parent as true and the
condition with the indicated truth value. Scope is `whole-program` or `cone-only`.
There is no witness for an empty side. `parent-unreachable` suppresses child noise;
`varying` also produces no condition diagnostic. `unknown.reason.kind`
is `unsupported`, `inconclusive` (with phase/resource), `deadline`,
`inconsistent-assumptions`, or `not-checked` when prerequisite work produced no report.
Missing example fields in an unperformed query must not be treated as absence proofs.
An inconsistent context still emits its existing context finding, never vacuous
condition notices. Cancellation withdraws the obsolete job.

Unknown results caused by unsupported meaning, limits or deadlines produce one
`unanalysed-condition` finding with the same `(verification, notice)` identity as
the other notice kinds. The message says the condition could not be analysed and
names the cause. Diagnostic `data.evidence.reason` retains `kind` and adds:

- `unsupported`: `blockingRegions`, an array of keyed components, each an array of
  atoms (`relation`, `arguments`). These are the blockers retained by the checker
  for the condition or enclosing scope, not all unsupported regions in the program.
- `inconclusive`: `phase` and `resource`, as in the summary.
- `deadline`: `phase` and `resource: "deadline"`.

`summary.notices` retains its existing shape: unsupported and deadline reasons have
only `kind`. Neither `inconsistent-assumptions` nor `not-checked` produces this finding.
All notice diagnostics remain advisory, including for CLI exit classification.

The optional `notices` selection list uses the shared resolver and permits only
notice names. Notice names and their relation references support navigation, hover,
outline, highlighting, formatting and validated rename across affected programs.

### Filtered world notes

Input observations range over the checked program's eligible input atoms. A
`within` provider excludes tuples from that universe entirely, including the absent
list; an authored negative premise on an excluded atom can still appear in proof
evidence. Restricted-domain preparation exhaustion uses the existing inconclusive
shape with phase `input domains` and the exhausted resource. No evidence schema or
finding identity changes.

Uniqueness and coverage retain their full observations in structured evidence.
Their human notes restrict those observations to checker-supplied structural
dependency-cone inputs: the union for the conflicting tuples in a uniqueness
finding, or for every candidate tuple of the missing coverage group.

Uniqueness evidence and each coverage example carry an additive
`dependencyInputs` field, using the same shape as emptiness below:
`{"state":"complete","inputs":[...keyed atoms...]}`,
`{"state":"incomplete","reason":{"phase":...,"resource":...}}`,
or null before collection. Complete empty scopes omit the input note; unavailable
scopes explicitly show the full observation. Collection has a separate allowance
per witness, so it cannot change semantic completeness. Inputs are projected to
semantic keys for session equality. This affects notes only; primary and related
locations are unchanged. No-meaning world notes keep their existing behavior.

### Coverage results

A coverage finding uses
`{"verification": [namespaceKey, name], "obligation": [namespaceKey, name], "component": "coverage"}`.
Program ownership remains `data.program`. Its identity is independent of displayed groups
and witnesses. Each retained missing-group example is placed on the locatable current
declarations of its constants in the checked program's own files; the obligation is
related. Several grouping columns and examples can produce several primaries with the
same `data.finding`. Shared locations merge their group/world notes and related
locations. When an example has no qualifying constant declaration (`group_by: ()`,
library-only constants or missing current spans), it keeps the obligation placement,
including the labeled library fallback. Upstream origins never supply primaries.
Only this constant placement lifts coverage's one-primary restriction; unsupported
and inconclusive coverage results still use the obligation. Uniqueness retains its
existing per-overlap-group reporting and identities.

Every diagnostic carries the same complete finding evidence, including all retained
examples, even though its visible notes describe only the groups placed there.
The finding inventory and summary remain one entry per obligation/verification.

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

### Exactly-one results

An exactly-one declaration uses the same coverage identity and payload as above. Its
uniqueness findings use the existing group object plus a top-level discriminator:
`{"verification": [namespaceKey, name], "group": {"obligation": [namespaceKey, name], "tuple": [...]}, "component": "uniqueness"}`.
Both identities refer to the same authored obligation. Program ownership remains
`data.program`; neither identity depends on the witness. Standalone `at_most_one`
findings keep their existing group identity without a component field; standalone
`at_least_one` findings are unchanged.

For exactly-one, `summary.groups[].identity` also includes `component: "uniqueness"`;
`summary.coverage` describes the coverage part independently. Uniqueness counterexamples
retain `replayed-counterexample` evidence and per-group reporting. A failed part keeps
the verification in `findings` even if the other is incomplete; the other part's reason
and diagnostic remain visible. A proof requires both parts to prove. Shared selection
notices and the empty-grouping-domain Information note apply unchanged.

### Emptiness results

An `empty(R)` finding uses
`{"verification": [namespaceKey, name], "obligation": [namespaceKey, name], "component": "emptiness"}`.
A replayed failure has primaries on the retained tuples' producing rules and facts,
narrowed to the ownership frontier for library obligations, as uniqueness does.
Premise occurrences and the obligation are related. Each tuple
is placed separately under normal program ownership and library fallback, then
shared primary locations are merged. Per-location notes name the tuple; a shared
location has each applicable tuple's note. "Inputs in dependency cone" shows
the observation restricted to the checker-supplied structural cone inputs, with
replay scope. This includes inputs behind negative derived premises and alternative
producers. A complete cone with no inputs omits the input note. If cone collection
is unavailable, a labeled fallback shows the full observation. The structured
observation and replay scope below remain complete and unchanged.
All diagnostics share the same finding identity, independent of examples and
derivations. Program ownership remains `data.program`. Findings without a witness
stay at the obligation.

`summary.emptiness` is present only when emptiness obligations are selected. Entries
contain `identity` (obligation and component), `outcome` (`proved`, `counterexample`,
`inconclusive`), `complete`, `unresolved` and `reason` (null or `{phase, resource}`).
`unresolved` means some permitted world could not be settled or certified; `reason`
records resource exhaustion. Either prevents proof. A known failure remains a
`counterexample` with `complete: false` when analysis elsewhere is unresolved.

Evidence uses `replayed-counterexample` with component `emptiness`, or `no-witness`
if there is no confirmed tuple. It carries the same `complete`, `unresolved` and
`reason` fields. Both the summary entry and evidence contain:

- `presentTuples: {count, exact}`: the number of distinct tuples confirmed present in
  at least one permitted world. Different tuples may require different worlds.
  `exact` equals `complete`; otherwise the count is a lower bound. Repeated worlds
  and derivations of the same tuple do not increase it.
- `examplesTruncated`: true when the confirmed count exceeds the retained sample.
  False does not assert completeness; consult `presentTuples.exact`.
- `examples`: the retained entries, the smallest confirmed tuples by semantic key.
  The editor retains up to three. API/CLI callers may request another bound or all
  confirmed tuples; the shape, finding identity and count semantics are unchanged.
  Each contains `tuple` (one keyed atom), its own `observation: {present, absent}`,
  `scope` (`whole-program` or `cone-only`), `producers` (retained producing-rule
  occurrence keys), `attribution` and `dependencyInputs`. Empty when no tuple was confirmed.
  `dependencyInputs` is `{"state":"complete","inputs":[...keyed atoms...]}`,
  `{"state":"incomplete","reason":{"phase":...,"resource":...}}`, or null before
  collection. Its inputs are ordered by semantic key. Collection runs after
  semantic checking with a separate bounded allowance per tuple, independent of
  source attribution; it never changes the verdict or checking completeness.

The former singleton `tuples`, `observation`, `scope` and `attribution` evidence
fields are replaced by those per-example fields. Evidence also retains top-level
`producers` for the whole finding. Other obligation kinds' payloads are unchanged.

Per-example `attribution` is `{"state":"complete"}` when its derivation was retained,
or `{"state":"incomplete","reason":{"phase":...,"resource":...}}` when bounded
attribution could not finish (null before the attribution pass). Each tuple has a
fresh attribution allowance. Exhaustion falls back to the obligation for that tuple,
with a note; it never changes semantic `complete`, `unresolved`, `reason` or the
count, and does not consume another tuple's allowance. Attribution completeness
describes evidence collection, not availability of source spans or upstream origins.

Blocked facts never serve as witness tuples. Diagnostic codes are `counterexample`
for a replayed failure and `inconclusive` otherwise; proof emits no diagnostic.
Current `.den` spans remain primary; embedded origins remain related and available
through Go to Origin.

### Configuration

`initializationOptions.denotate` or
`workspace/didChangeConfiguration {settings: {denotate: {timeoutMs}}}`:
`timeoutMs` defaults to 10000 and bounds each verification's check separately, so a
program with several verifications may take that long per verification. An update
replaces the whole object. There is no backend setting: BDD is the only implementation.
The `backend` fields in status and summaries remain fixed BDD metadata for compatibility
and result identity; they do not select an algorithm. Obsolete backend configuration
properties are ignored like other unknown configuration properties.

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
