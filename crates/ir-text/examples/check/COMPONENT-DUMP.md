# Admission component dumps

```sh
just check-den ROOT --dump-component component.jsonl
just bench-den-schema --source PROGRAM.den --dump-component component.jsonl
```

The first command creates a new file at the given path. The schema runner accepts
one file name and keeps it inside the new run directory; `run.json` and recovered
`report.json` retain its path. Existing files are never replaced. The file contains
program names, source URIs and source ranges. It is a local diagnostic artifact,
not an anonymized export or a new editor protocol.

The stream is versioned JSON Lines. Each complete line is an independent record.
Records are flushed as they are produced. Read a partial file through its last
complete line after an interrupted process. A cooperative admission deadline or
cancellation also records the last committed graph. A process killed by the OS
cannot write a final graph; the earlier attempt records remain useful.

Every data record carries a verification identity and snapshot number. Identities
are SHA-256 digests of semantic keys using the version-1 encoding; they do not use
arena handles or source offsets. Snapshot numbers are invocation-local references,
not stable identifiers. Compare structural content without these numbers across
runs. Locations are source URIs with half-open UTF-8 byte ranges, directly usable
against the named source. Structural sections are sorted by semantic key.

- `graph-begin` records completion, interruption or actual shared-admission reuse.
  Its graph is the last committed state, never a partly installed rewrite batch.
- `component`, `atom`, `rule` and `dependency` describe remaining negative-cycle
  components and their boundary premises. Rules contain signed premises, their
  settled/unresolved classification, signed settled premises and existing Boolean
  replacement expressions. `structure-end` marks a complete structural section.
- `context`, `assumption` and `exclusive-group` record selected restrictions only.
  The context is their conjunction, W. Group membership lists represented ground
  tuples for each explicitly selected uniqueness restriction; it does not infer
  new exclusive groups or enumerate absent Cartesian-product tuples. These follow
  structure so a large context cannot prevent recording the component itself.
- `attempt` records the candidate's guard, implied-guard expression, relaxed
  producer, pruning status and before/after sizes at the snapshot actually used
  for bounds. G is the conjunction of its signed settled premises, replacement
  expressions and optional implied guard. The evaluation domain is G AND W.
- `implied-source`, `cone-atom`, `cone-producer`, `dead-producer` and
  `pruning-source` preserve that attempt's sources, live markings and deadness
  reasons. They are captured before those temporary objects are released.
  `cone-input` is a structural dependency read set of G and live producers' settled
  premises and replacements; W is described separately by the selected restrictions. It is **not** a Boolean formula and is not substituted
  for G. `attempt-data-end` says that section was recorded completely.
- `attempt-outcome` distinguishes a constructed settlement certificate, a negative
  result, a local resource skip (phase, resource, limit and observed demand), a
  certificate-size cutoff, and failure. A settlement certificate is a proposal;
  the final graph shows what was committed. A failed preparation can have an
  outcome without a cone. Ranking previews that succeeded are not reported as
  bounds attempts. A pruning fallback is separate from the attempt's outcome.
- `graph-end` marks completion of structure and context. Reuse has no fresh
  attempts. Attempt traces from fresh and reused runs therefore differ honestly.

`--dump-component-limit N` sets the aggregate data-record cap (default 100,000).
The independent diagnostic allowances also bound traversal to 2,000,000 work
units, serialized data to 32 MiB, copied name text to 32 MiB and active recording
time to 10 seconds. Each collection is limited to 16,384 entries, and expression
formatting to depth 128. Half of the aggregate allowances is reserved for attempts,
half for final graphs and contexts, across all verifications in the file. Small
header and truncation records, including markers for verifications skipped after
recording stopped, are outside the data allowance.
The allowances are provisional diagnostic controls, not checker policies or exact
heap-byte limits; checks are cooperative, including around formatting and IO.

`truncated` identifies an exhausted section. Completed sections report exactly
zero omitted records. On record/byte exhaustion the omitted count is a lower
bound; other interrupted traversal reports an unknown count. The writer never
continues traversing just to count omissions. Creation, writing or diagnostic
exhaustion issues are reported on stderr even with `--no-progress`; ordinary
stdout, checker budgets, findings and exit codes are unchanged. Recording time is
excluded from admission's deadline without resetting time already spent checking.
