# Roadmap

Ordered roughly by priority. The first real programs are expected to be written
directly in `.den`.

## Contract vocabulary: follow-ups

`at_most_one`, `at_least_one`, `exactly_one` and `empty` are implemented; see
[the format](den-format.md#coverage-obligations). Deferred until real programs ask
for them: "why not derived" explanations for coverage failures, conditional group
eligibility, and assumption forms beyond input `at_most_one`.

## Authoring robustness

Error recovery while rules are incomplete, latency at realistic sizes, and `.den`
formatting, driven by what goes wrong in the first real programs. Known items:

- [Obligation diagnostic placement](proposals/obligation-diagnostic-placement.md):
  emptiness reports a bounded set of tuples, each on its own derivation. Next:
  coverage failures on the missing group's constants, then ownership-frontier
  narrowing. Explicit targets, alternative derivations and per-tuple identity are
  deferred until a real program needs them.
- Explain unsupported negation cycles. When a redundancy proof fails, show the
  permitted world where the guards overlap and the consistent answers it allows, and
  suggest the fixes (an assumption that excludes the inputs, or giving one case
  priority). Today the diagnostic only says the cycle is unsupported.
- Exported DSL libraries can show singleton-variable warnings that the user cannot act
  on; print singletons as `_` or skip style lints on generated/library files.
- Each Go to Origin and rename request rebuilds snapshots and reloads programs
  synchronously; origin restoration scans the corpus per statement. Fine at current
  sizes; revisit with real programs.
- Unchecked-obligation notices and verification status load the program a second
  time, synchronously on the server loop, at each snapshot change so they are
  available before checking finishes. Derive them from the incremental index instead
  if this shows up as editing latency.

## Refactoring by semantic equivalence

Support refactorings that do not preserve IR structure but preserve meaning: inline or
extract a helper relation, merge or split rules, simplify guards. A refactoring from P
to P′ is valid if, for every permitted input world, the least fixed points agree when
**projected onto the observable interface**.

- **Observable interface:** the DSL library or `.den` author marks observable
  relations (for the test DSL, classifications such as `slot_value` and `available`);
  others are internal helpers that may change. Inputs are always part of the interface;
  generated helpers are always internal. Needs IR support and round-tripping `.den` syntax.
- **Approach:** BDD fact conditions are canonical under a shared input order, so
  equivalence is equality per observable fact and the difference is a counterexample
  world. Inconclusive within limits means refuse; alternative solvers require a
  demonstrated need under the [backend policy](checker-policies.md#backend-retirement).
- **Sequence:** an equivalence API in the checker; rename uses it as a
  syntax-independent validator; then refactoring commands.
- **Open:** whether obligation verdicts are always compared or obligation relations
  must be observable; interface syntax; refactorings that change W, domains or the
  input schema are out of the first version.

## Test DSL language services

Definition, references, hover, rename and possibly quick fixes for the test DSL. When
built, extract the `.den` editor's validated-rename engine into shared code, designed
against both editors, and generalize the root catalog when test DSL programs
become multi-file.

## `.den` scorecard support

Accept `.den` programs in the scorecard, to re-score the provisional
[checker policies](checker-policies.md) on real programs. It runs verifications
through the same request API as `check-den`, comparing variants only within the same
verification.

## Research: admission by well-founded totality

A sound, symbolic way to admit cycles through negation. The reduct operator Γ is
antimonotone, so Γ² is monotone; its least and greatest fixed points L and U bound
every stable model (the alternating-fixpoint construction of the well-founded
model). Where L = U in a world, that world has exactly one stable model, so a
component whose bounds agree is admitted there. This adopts no third truth value:
the bounds only prove that a unique two-valued meaning exists.

- **Approach:** compute L and U as BDD conditions per fact under the selected
  assumptions; the component is admitted on the worlds where L and U agree for all
  of its atoms. This generalizes per-world certification (`certify_observation`)
  to all worlds at once, and fits cycles that input guards break world by world.
  Facts in L or outside U can also prune no-meaning searches.
- **Limits:** totality is sufficient, not necessary (`a :- not b. b :- not a.
  a :- b.` has one stable model but a non-total well-founded model), so it
  complements discharge rewrites and certification. It proposes no edit, so it needs
  its own evidence kind and wording, and a recorded admission decision.
- **Trigger:** real programs with unsupported regions that their input guards
  resolve per world but discharge cannot. Prototype on one component and validate
  against the stable-model oracle and certification. Background: approximation
  fixpoint theory (Denecker, Marek, Truszczyński).

## Small items

- Richer assumption forms (beyond input `at_most_one`) must establish that the selected
  assumptions permit some world before checking, reporting `inconsistent-assumptions`
  otherwise; today every assumption permits the all-absent world.
- Let library authors mark obligations as offered but not checked by default, to quiet
  per-consumer notices for menu-style libraries.
- Per-verification scope (domains); today every verification uses its program's domains.
- The test DSL editor treats each open file as one program; composing companion `.den`
  files (extra verifications over an export) is unscoped integration work.

- Trim the unused module/file-based analysis in `crates/analysis`, left from an earlier
  editor prototype.
- Include/exclude lists for the CLI's `den.root` folder scan, which currently also
  walks `.git`, `node_modules` and `target`.
