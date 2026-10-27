# Obligation diagnostic placement

Status: proposed, not implemented. Recorded 2026-10-27. The first increment needs no
new syntax; explicit diagnostic targets are deferred.

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
label declaration directly. Today an `empty` finding has one primary at the
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
  producer in that world, not every alternative derivation.
- Repeated identical authored facts are separate rule occurrences with separate
  origins, but the derivation selects one, as for uniqueness. Showing the other
  occurrences of the same ground fact is a separate, bounded enhancement for both
  kinds.
- Positive premises are all part of the derivation. A rule such as
  `invalid(N, L) :- node_label(N, L), node_kind(N, K), !allowed(K, L);` also places
  the `node_kind` fact as a primary. This noise is accepted for now; narrowing is
  what explicit targets are for.
- `empty` reports one example tuple. Locating it well does not report every invalid
  tuple; bounded enumeration of present tuples (like coverage's retained examples) is
  a separate usability follow-up, likely soon after this increment.

## Deferred: explicit diagnostic targets

Explicit targets (**blame facts**) remain useful where derivations do not help:

- **Coverage.** A missing group has a witness of absence but no violating tuple to
  derive. If `exactly_one(node_label, group_by: node)` fails coverage for `n1`, an
  author could target present uses such as `edge(n1, _)`, matching existing tuples
  without inventing values. Coverage still ranges over resolved grouping domains;
  targets never change which groups require coverage.
- **Narrowing noisy derivations,** when positive declaration premises should not be
  primaries.

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
- Existing uniqueness, coverage and test DSL behavior is unchanged. Tests compare
  outcomes, identities and placement, never budgets or timings as goldens.

## Current implementation and owning documentation

`PresenceExample` in [the emptiness checker](../../crates/check/src/emptiness.rs)
retains the tuple, observation and replay scope; it gains the derivation evidence,
including its keyed session form for cold/warm agreement. [Shared
presentation](../../crates/presentation/src/evidence.rs) reuses the uniqueness
contribution code. The [development CLI](../../crates/ir-text/examples/check.rs) prints
only the status summary, not diagnostics and notes; printing them is a separate,
small improvement.

This changes a documented decision: emptiness placement is currently "at the
obligation, independent of the selected example" ([format](../den-format.md#emptiness-obligations),
[protocol](../../crates/den-lsp/PROTOCOL.md), [decisions](../decisions.md)). Update all
three. Identity stays independent of the example; placement follows it. Keep
implementation sequencing and handoffs in local `plans/`. The
[roadmap](../roadmap.md#authoring-robustness) needs only a short pointer.
