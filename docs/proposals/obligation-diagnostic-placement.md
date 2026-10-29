# Obligation diagnostic placement

Status: derivation placement, bounded emptiness enumeration, dependency-cone
world notes and coverage placement on missing-group constants implemented
2026-10-27/28, with no new syntax. Next: ownership-frontier narrowing. Explicit
targets, alternative derivations and per-tuple identity are deferred, with reasons
below.

## Problem

A library obligation can identify an error correctly while placing its diagnostic
at the obligation declaration rather than the DSL construct the author must fix.

For example, a lowerer records each authored label on a node as a fact:

```den
node_label(n1, l1);
```

The library derives an error when a label is not allowed on that node:

```den
invalid_label(N, L) :-
    node_label(N, L), !allowed_label(N, L);

obligation allowed_labels: empty(invalid_label);
```

The useful primary location is the authored `node_label` occurrence. In a `.den`
editor, highlighting it makes Go to Origin available at the relevant fact. A bespoke
DSL editor can use that occurrence's upstream provenance to highlight the original
label declaration directly. Previously an `empty` finding had one primary at the
obligation, using the labeled fallback for library declarations.

## What already works: uniqueness follows its derivation

An `at_most_one` counterexample retains, for each conflicting tuple, the grounded
derivation that produced it in the replayed world (`collect_evidence` in
[findings](../../crates/check/src/findings.rs)). Presentation places the rules of that
derivation as primaries and their premise literals as related locations; the
obligation is related. Program ownership and the library fallback apply as usual.

This already gives exact, world-specific attribution without author syntax. With
guards lowered as helper rules, a conditional conflict highlights the rules that
actually fired in the counterexample world:

```den
relation guard_a();
guard_a() :- kind(n1, k1);
guard_a() :- kind(n1, k2);
labelled(n1, l1) :- guard_a();
labelled(n1, l2) :- flagged(n1);
obligation one_label: at_most_one(labelled, group_by: node);
```

With `kind` and `flagged` as inputs, if the counterexample world has `kind(n1, k2)` and
`flagged(n1)`, the primaries are the
two `labelled` rules and the `kind(n1, k2)` branch of `guard_a`, not the `k1` branch.
Matching authored facts by tuple values could not make that distinction. A library
check whose conflicts are produced by consumer-authored rules therefore needs no
framework change to be located well.

## First increment: emptiness uses the same placement

An `empty(R)` failure already confirms a present tuple in a concrete world. Retain that
tuple's grounded derivation with the example, as uniqueness does, and present it the
same way: derivation rules as primaries, premise literals related, the obligation
related.

Take the evidence from whichever replay confirmed presence. Ordinary replay can stay
blocked while certification establishes the tuple; then the derivation comes from
the certified evidence, as uniqueness already extracts it, not from the blocked
replay.

In the example above, the derivation of `invalid_label(n1, l1)` is the library rule
and the consumer's `node_label(n1, l1)` fact. The fact is owned by the consumer and
becomes a primary there; the library rule follows the existing ownership and
fallback policy. `allowed_label` is a negated premise: its literal occurrence is
related, and no fact is blamed for an absence.

Contract:

- Placement only. Verdict, completeness, finding identity and ownership are unchanged;
  one finding may have several locations, as uniqueness findings already do.
- Cold and warm sessions place the same failure identically. Placement now follows
  the reported example, so example selection and derivation choice must be
  deterministic under semantic keys, as for uniqueness.
- Attribution never changes checking. Emptiness keeps searching after its first
  example, so collect placement evidence after semantic checking, under its own
  bounded work, not the checking budget. If it runs out, the known counterexample
  stands and placement falls back to the obligation with a separate attribution
  status. It never sets the semantic `inconclusive` field.
- Uniqueness and coverage placement, obligations without failures and the test DSL
  expectations are unchanged.

Known limits of this increment:

- One grounded derivation per tuple: the first found in replay. It names an exact
  producer in that world, not every alternative derivation. Several authored
  declarations producing the same invalid tuple therefore need not all be
  highlighted.
- Repeated identical authored facts are separate rule occurrences with separate
  origins, but the derivation selects one, as for uniqueness. Showing the other
  occurrences of the same ground fact is a separate, bounded enhancement for both
  kinds.
- Positive premises are all part of the derivation. A rule such as
  `invalid(N, L) :- node_label(N, L), node_kind(N, K), !allowed(K, L);` also places
  the `node_kind` fact as a primary. This noise is accepted for now; see the
  ownership frontier below for the next narrowing candidate.

## Implemented: several emptiness tuples per finding

`empty` now retains up to three distinct replay-confirmed tuples, ordered by semantic
key, each with its own world, replay scope and attribution. Checking continues to
count confirmed tuples beyond the retained sample. The count is exact when checking
completes and a lower bound otherwise; it counts tuples across permitted worlds,
not tuples necessarily present together.

Retention preserves semantic scan order and work charges. Attribution runs after
checking with a fresh bounded allowance per tuple. One tuple exhausting attribution
does not affect another tuple or semantic completeness. Place each tuple separately,
then union the locations; notes name the tuple, merging at shared locations.
Input notes show the observation restricted to each tuple's structural dependency-cone
inputs, supplied by the checker and projected to semantic keys for sessions. Unlike
the retained proof's leaves, this scope includes inputs behind derived absences and
alternative producers. Omit the input note for a cone with no inputs. Cone collection
runs under its own bounded allowance; exhaustion falls back explicitly to the full
world without changing checking completeness or attribution. Structured evidence
retains the full world and the separate scope status. A tuple's obligation fallback
remains visible even when another tuple has producing-rule locations.

Finding identity stays at obligation/component/verification. Fixing one error does
not replace the remaining errors' finding. Per-tuple identity is deferred until
suppressions, waivers or another consumer needs it; see [decisions](../decisions.md).
The cap bounds the number of retained tuples, not the number of locations in their
derivations. Ownership-frontier narrowing and explicit targets are still separate.

Behavioral checks cover the cap and exact/lower-bound counts, key order, separate
worlds, fixes preserving identity, shared locations, independent attribution
exhaustion, and cold/warm agreement. Existing uniqueness, coverage and test DSL
expectations remain unchanged.

## Implemented: coverage failures on the missing group's constants (2026-10-28)

A coverage failure has no violating tuple. Previously it was placed at the obligation,
through the labeled fallback when a library declared it. The missing group, however,
consists of constants that usually have authored declarations in the consumer. For
`exactly_one(node_label, group_by: node)` missing `n1`, the actionable location is
`const n1: Node;`; previously the author had to read the note and find `n1`
themselves. A missing annotation in a consumer could land in the library file.

Implemented placement, with no syntax:

- For each retained missing-group example, the declarations of the group's constants
  that are in the checked program's own files and locatable are primary; the
  obligation is related. With several grouping columns, each such constant's
  declaration is primary. Retained examples are unioned, merging their notes at
  shared locations.
- Fallback to current placement when no group constant qualifies: `group_by: ()`,
  constants declared only in libraries, or missing spans.
- Placement only, from the group already in the evidence: no new checking, no change
  to which groups require coverage, and finding identity stays one coverage finding
  per obligation/verification. The one-primary restriction for coverage
  findings is lifted only for this case.

Acceptance: a missing group highlights its constant's declaration; adding the missing
fact clears it; a library-declared constant and `group_by: ()` keep current placement;
several missing groups union their locations; cold and warm sessions agree; renaming
or moving the constant moves the diagnostic. Emptiness and uniqueness are unchanged.

## Next increment: narrowing at the ownership frontier

Evidence from the first real library: it decodes finite observation codes into values,
and the consumer lowers guards as helper rules. One conditional conflict between two
consumer rules that each produce `labelled(n1, _)` placed nine primaries under one
finding identity: the two producing rules (essential), four guard helpers that fired
(useful context), and three decoding and type-declaration facts reached through the
library's decoding rule (noise). Value-matched explicit targets would be the wrong fix:
they would point at declarations rather than the producing rules, lose which guard
fired, and highlight every matching declaration rather than the active one.

Proposed narrowing, with no syntax. It applies only to obligations declared in a
library; obligations declared in the checked program's own files keep current
placement. The boundary is the checked program's own files versus its whole library
dependency closure, using the ownership information presentation already receives;
the checker stays independent of program roots.

- **Traverse producers, not contributions.** Walk the positive-support edges of the
  retained proof from each reported tuple, deduplicating shared support rather than
  enumerating paths. Inspect the source occurrence of each producing rule, including
  empty-body facts. Relation declarations, constants and premise literals never stop
  the walk; negative premises stay related.
- **Frontier.** On each branch, the first producer that is in the program's own files
  and locatable is primary. An unlocated generated rule does not stop the search for a
  deeper locatable consumer producer. Everything else in the derivation stays
  related, not dropped.
- **Union across roots.** A producer that is the frontier for one reported tuple is
  primary even if it lies below the frontier for another.
- **Fallback.** If a reported tuple reaches no locatable consumer producer, including
  branches that end in input leaves, its placement stays as today.
- **Placement only,** from the same retained derivation: no new evidence, verdict,
  identity or attribution status.

In the conflict above, the two consumer rules are primary and the fired guards and
decoding facts are related. For `empty`, library rules lead to the consumer's authored
fact, which stays primary, as today. A library rule with two positive consumer
premises still makes both primary; choosing among those is left to explicit targets.

## Deferred, with reasons

These are deferred until a real program shows the need, not scheduled.

### Explicit diagnostic targets

Explicit targets (**blame facts**) were motivated mainly by coverage. Placing coverage
failures on the missing group's constants covers the observed case without syntax.
What remains:

- **Coverage where the constant's declaration is the wrong place,** for example when
  the actionable location is a use such as `edge(n1, _)`. A target could match
  existing tuples without inventing values; coverage still ranges over resolved
  grouping domains, and targets never change which groups require coverage.
- **Choosing among frontier occurrences,** when several consumer premises of one
  library rule reach the frontier and only some are actionable.

Neither has appeared in a real program, while the cost is high: syntax, IR
representation, shared resolution and rename, validation, bounds and truncation
reporting. They may never be needed.

Contract to keep when they are built:

- A target selects **all matching authored occurrences**, not exact producers:
  value matching cannot tell which of two matching declarations was active.
  Derivation placement is the exact mechanism.
- Eligible occurrences are explicit, ground, empty-body facts. Tuples available only
  through rules or runtime inputs never match; a relation may hold both, and only its
  eligible fact occurrences participate. No match falls back to the obligation, and
  is not an invalid program.
- Targets are validated at load (relation, binding columns, sorts), apply per
  component (for `exactly_one`, coverage and uniqueness separately), keep finding
  identity unchanged, and are bounded; truncation is reported separately from the
  unchanged verdict.
- A target must hold in the counterexample world. Authored facts hold in every world;
  input-dependent targets would need checker confirmation, never presentation-side
  evaluation.

Syntax, the IR representation and the incomplete-location payload are settled before
that work starts.

### Alternative derivations and repeated authored occurrences

One derivation per tuple is retained, so other declarations producing the same tuple
(a bidirectional declaration contributing both directions, or a repeated identical
fact) are not all highlighted. In practice this corrects itself: fixing the
highlighted occurrence leaves the tuple present, and the next check points at the
remaining one; when the real fix is a shared declaration, it clears all of them.
Expansion would need bounds and interacts with frontier narrowing.

### Per-tuple finding identity

One finding per obligation already gives one diagnostic per located tuple, and
fixing one error leaves the others' identity intact. Per-tuple identity pays off only
when something tracks individual errors, such as suppressions or approved
exceptions; introduce it with that feature ([decisions](../decisions.md)).

## Acceptance examples

- An invalid label highlights its authored fact in the consumer; valid labels do not;
  library rules in the derivation follow the existing fallback.
- A negated premise is related, never a blamed fact.
- Warm editing, with verdict and finding identity unchanged in both cases: moving the
  blamed `.den` fact moves its primary diagnostic; editing only its embedded
  `loc(...)` updates the upstream related location and the Go to Origin destination,
  and does not move the `.den` primary.
- Cold and warm sessions agree on placement for the same failure.
- Presence confirmed only by certification is placed on the certified derivation.
- An attribution limit keeps the counterexample, falls back to the obligation and
  leaves completeness unchanged; checking completeness is the same with and without
  attribution.
- First increment: existing uniqueness, coverage and test DSL behavior is unchanged.
  Tests compare outcomes, identities and placement, never budgets or timings as
  goldens.

Ownership-frontier increment (it intentionally changes uniqueness placement for
library-declared obligations):

- Two consumer producers of a conflict are primary; guard helpers and declarations
  below them are related.
- A library rule with two positive consumer premises keeps both primary.
- Transitive libraries: an intermediate library rule does not become the frontier;
  the consumer producer below it does.
- Shared support: a producer that is the frontier for one tuple stays primary when it
  is deeper for another.
- Input leaves and missing spans fall back to current placement; an unlocated
  generated rule does not hide a deeper locatable consumer producer.
- Obligations declared in the checked program's own files keep current placement.
- Cold and warm sessions agree, and placement follows current provenance after edits.

## Current implementation and owning documentation

`PresenceExample` in [the emptiness checker](../../crates/check/src/emptiness.rs)
retains each tuple, observation, replay scope and separate attribution evidence/status.
Its `EmptinessSummary` carries the bounded examples and count, with keyed evidence for
cold/warm agreement. [Shared presentation](../../crates/presentation/src/evidence.rs)
reuses the uniqueness contribution code. The [development CLI](../../crates/ir-text/examples/check.rs)
now prints these presented diagnostics, notes and labeled related locations by
default, grouped by verification; `--json` retains its status-summary output.
Default CLI related-location output expands producing rules, the checked obligation
and upstream origins; `--verbose` expands the rest. This CLI layout does not change
placement or the editor's related information.

Uniqueness and coverage world notes now use structural input-cone filtering too:
conflicting tuples for uniqueness, all candidate tuples of each missing group for
coverage. Full replayed worlds remain in evidence. This reduces world-note noise
independently of the still-deferred ownership-frontier narrowing.

The [format](../den-format.md#emptiness-obligations),
[protocol](../../crates/den-lsp/PROTOCOL.md) and [decisions](../decisions.md) now record
the change from obligation-only placement. Identity stays independent of the example;
placement follows it. Keep implementation sequencing and handoffs in local `plans/`.
The [roadmap](../roadmap.md#authoring-robustness) needs only a short pointer.
