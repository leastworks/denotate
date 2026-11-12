# denotate-editor

Language-independent LSP mechanics shared by the `.den` editor and the test DSL
editor. Frontends supply their grammar, checking closure and publication policy; this
crate contains no roots, manifests, ownership rules, filesystem policy or DSL concepts.

| Module | Responsibility |
| --- | --- |
| `document` | Text/tree snapshots, UTF-16 positions, transactional edits, incremental parsing |
| `synchronization` | `Documents<D>`: retained documents, rejected versions, full-text recovery |
| `lifecycle` | Document notification decoding, version-safe changes, stored/removed/sync-loss hooks |
| `publication` | Versioned diagnostics and one-time withdrawal on synchronization loss |
| `transport` | Notification sending, serial dispatch, cancellation checkpoints, shutdown, stdio |
| `checking` | `Scheduler`: serial worker, per-context checker sessions, FIFO coalescing, cancellation, revision tickets, checkpoint holds, cold reset |
| `checking_server` | Bounded owner loop: queued edits before finished results, a bounded batch of messages per turn, next job after each turn, shared test protocol |
| `presentation` | Immutable finding spans to LSP locations, sharing the buffer line/column helper |
| `workspace_edit` | Canonical editability checks, byte-span mapping, versioned workspace edits with a stale-snapshot check |
| `test_support` | Fast `validated`/`idle` barriers and an async frontend-ready barrier |

## Using it

For a batch of findings, share `presentation::Locations` across the batch. It
indexes each immutable source snapshot once and preserves LSP UTF-16 positions
and CR/LF/CRLF boundaries. Single-location convenience functions remain available;
columns still scan within the containing line.

A frontend calls `parser(language)`, wraps `Document` as needed and implements
`transport::Handler`. Worker-backed servers implement `checking_server::CheckingHandler`
and `lifecycle::Lifecycle`.

The scheduler's contract: allocate a ticket before preparing a snapshot, then enqueue a
payload or cancel the context. A replacement keeps its queue position; a replacement for
the running context joins the tail. Cancellation keeps the session warm; `close`
releases it. At publication, `complete` runs the frontend's "still current?"
predicate; publication itself stays with the frontend.

`CheckingHandler::checking_status` is an optional owner-thread hook after updates
and starting the next job, before checking-idle responses. A frontend can publish
deduplicated progress from current states there. Progress never bypasses the
frontend's freshness checks or changes the worker's semantic budgets.
`Scheduler::spawn_with_progress` additionally supplies a typed report callback;
`Event::Progress` carries the same ticket as the result. Frontends discard stale
updates. Progress-only owner turns skip snapshot reconciliation, and each turn
consumes at most one worker event so a phase update can be observed before the next.
The default progress type is uninhabited; ordinary `spawn` callers emit none.

`workspace_edit::editable` checks workspace containment by canonical path, protected
folders (`DEFAULT_PROTECTED_FOLDERS`: `generated`, `node_modules`, `dist`, `.git`) on
both canonical and visible paths, and real write access without truncation.
`assemble` produces `documentChanges` with client versions (null for closed files) and
compares the caller's observation stamp just before returning.

## Checking test protocol

Enabled only with `DENOTATE_TEST_MODE=1`. Deterministic barriers and checkpoints, not
latency measurements.

| Method | Meaning |
| --- | --- |
| `denotate/test/checkingIdle` | Deferred request; answered once the scheduler is idle and the frontend's readiness gate is settled. Cancellable. |
| `denotate/test/hold` | Hold the next started job at `beforeResult` (default) or `duringCheck`. |
| `denotate/test/checkpoint` | Notification with the ticket identity when a held phase is reached. |
| `denotate/test/release` | `{revision}`: release that hold, or an invalid-parameters error. |
| `denotate/test/resetChecks` | Only when idle: release sessions; the frontend requeues current snapshots cold. |
| `denotate/test/checkingStats` | `started`, `finished` and `pending` records plus optional frontend measurements. |
| `denotate/test/checked` | Notification after an accepted completed check is published. |

Ticket identities are frontend-defined: the `.den` server uses `{program, revision}`,
the test DSL `{uri, revision, version}`. `denotate/test/idle`, `frontendReady` and
`validated` are fast barriers and never mean checking-idle.

```sh
just test-crate denotate-editor
```
