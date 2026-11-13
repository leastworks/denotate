# Roadmap

Ordered roughly by priority. The first real programs are expected to be written
directly in `.den`.

## Admission of negation cycles

Admission decides whether every permitted world has exactly one meaning. Implemented:
structural reduction (true/false propagation, dead rules, same-head subsumption after
bounded unfolding), producer removal by exact coverage, bound-based removal (a cyclic
producer whose bounded body is covered by exact producers), negation discharge and
cycle upper bounds, failure-local skips with precise retry, reuse of completed
negative attempts across rounds, and cycle-first ordering (see [decisions](decisions.md) and [checker policies](checker-policies.md)).
Cycle-relevant proofs and supporting evaluation precede downstream work; downstream
exhaustion is reported separately without relabeling the cycles' results. A
production-scale lowered program showed what remains:

- **Guarded settlement.** A cycle edge can be dead under the guard of the rule that
  reads it, one or more rules away from the negation. Settle the premise under that
  guard when bounds make it exact there, rewriting only into settled literals. Plain
  negative unfolding is not used: it can lose stable models (`h :- not p. p :- not h.`
  unfolded gives `h :- h.`).
- **Never-active cycles.** More generally, a component whose active dependency graph
  is acyclic in every permitted world (edges labelled with their guards, checked by a
  symbolic topological peeling) has one meaning per world without any rewrite. It
  needs its own evidence kind and evaluation path, and is the same check a schedule
  needs (below).
- **Wide heads.** A head with tens of thousands of producers can dominate a run even
  downstream, since obligations may read it. Check each removal candidate against
  the exact producers by subtraction (stop when nothing is left) instead of building
  their union; retain successful summaries, coverage and bounds across rounds when
  their inputs did not change.
- **Totality and loop formulas** remain research ([below](#research-admission-by-well-founded-totality)).

Cycles that are genuine, with two meanings in some world, belong to the lowering:
no sound checker can choose between them. See lowering guidance below.

## Testing at scale: shape, not just size

Most scale regressions so far were superlinear scans that small, tutorial-shaped
programs never exposed; budgets guarantee termination and honest results, not
throughput. `just bench-den-schema` generates incremental-schema programs at scale
(Shipping News vocabulary) and runs the real CLI with memory profiles and optional
sampling ([profiling](../DEVELOPMENT.md#profiling)). Next:

- **Layout-valid coupling:** cross reads only to fields decided earlier in an
  explicit, recorded execution order, so large generated programs resemble ones a
  DSL scheduler accepts, with an oracle for presence versus visibility.
- **Shape zoo:** DSL-independent families (fan-in, breakable and genuine negative
  loops, certification pressure, removal-heavy replay, presentation), each swept over
  sizes with per-phase growth exponents fitted only on completed phases, reported
  against both the knob and measured sizes, as advisory triage signals.

## Lowering guidance

Denotate is generic for stratified programs and for programs that follow a DSL's own
evaluation order. Advanced Shipping News lessons will show an incremental schema
(formats, expected and accepted fields, recognition) lowered three ways: directly
(unsupported, with both meanings shown), with a coverage rule (admitted), and with
assumed acceptance plus consistency and recognition assumptions (admitted). A second
lesson and a short reference page cover designing a lowering: follow the DSL's
evaluation order, defaults without priority, assumptions versus obligations, each
element's source of truth (message, computation or neither), fixed catalogs, and
reading unsupported or inconclusive results.

## Schedules from admitted programs

An admitted program's dependency order is an evaluation order valid in every
permitted world; admission's rewrites justify each early decision. A schedule check,
before any code generation, would project that order onto the lowerer's statements,
add producer edges for inputs produced during execution (including assumed inputs),
accept cycles that are never active or are broken by an early decision proven
equivalent under the permitted worlds, reject the rest with a cycle and a witness
world, and export the guarded schedule for comparison with a DSL's own scheduler.

## Contract vocabulary: follow-ups

`at_most_one`, `at_least_one`, `exactly_one` and `empty` are implemented for obligations
and [selected assumptions](den-format.md#selected-assumptions), including independently
stratified derived constraints and consistency checking. Deferred until real programs
ask for them: "why not derived" coverage explanations, conditional group eligibility,
and explanations of which selected assumptions conflict.

- **Assumption cones admitted under other assumptions.** Validation now uses a view
  specialized by exact fixed truth, shared with the computation of W, so cycles that
  exist only through fixed-dead instances no longer invalidate a cone. Runs now
  ground-validate only assumptions selected by their executed verifications;
  unselected ground cones get advisory deferred-validation diagnostics. Next, per
  verification and in layers: an assumption whose cone has negative cycles joins
  when admission under the assumptions already established resolves them (a least
  fixpoint, so no assumption justifies its own cone). Validity then becomes relative
  to a selection; unselected declarations keep structural validation.

- **Severity on obligations.** Every obligation failure is an Error today. Let a
  declaration choose Error, Warning or Information, where Warning and Information do
  not fail the verification or the exit code: for library rules that should warn
  rather than fail (style rules, deprecations, suspicious but legal choices).
  Trigger: a real library needing a warning-level rule.
- **Existential obligations.** All current forms are universal ("in every permitted
  world"). A `possible(R)` form would require R to hold in some permitted world, the
  negation of `empty(R)`: for example, every decision-table row or mapping must be
  able to apply (dead-rule detection). A failure has no counterexample world to
  replay, so it needs "why not derived" explanations (which premise or constraint
  always blocks it) and usually Warning severity. With both in place, condition
  notices (`varies`) could be defined in terms of them without changing their
  behavior. Trigger: a real program needing reachability requirements.

## Authoring robustness

Error recovery while rules are incomplete, latency at realistic sizes, and `.den`
formatting, driven by what goes wrong in the first real programs.
[Contextual condition notices](den-format.md#contextual-condition-notices) now report
impossible and always-true conditions within an explicit scope. Formula sharing and
proved simplification remain separate work. Known items:

- [Obligation diagnostic placement](proposals/obligation-diagnostic-placement.md):
  emptiness reports a configurable sample of tuples, each on its own derivation; coverage
  failures highlight the missing group's consumer constants. Library counterexamples
  narrow primaries to the first consumer producers along retained support.
  Explicit targets, alternative derivations and per-tuple identity are
  deferred until a real program needs them.
- Explain unsupported negation cycles further. Diagnostics now show the retained
  ground dependency path with concrete arguments and negative edges. When a
  redundancy proof fails, show the permitted world where the guards overlap and the
  consistent answers it allows, and suggest the fixes (an assumption that excludes
  the inputs, or giving one case priority). Those world-specific explanations remain
  separate from the structural cycle path.
- Generated helpers can change recursive meaning. The normalizer cancels double
  negation within one expression, but a relation boundary stops it: `t :- not not t`
  is `t :- t`, whereas `w :- not t; t :- not w; t :- t` is an unsupported negative
  cycle. Today's rule is to normalize each whole formula before introducing helpers
  and to share only identical normalized output. Two prospective options, if real
  programs need more; both change meaning for some programs, so each is a semantic
  decision to review against today's behavior, not merely stronger admission:
  - Normalize to negation normal form so generated helpers never appear negated
    (Lloyd–Topor currently negates helpers for negated conjunctions). Compare all
    affected programs with today's normalizer before adopting it.
  - Treat certain helpers as transparent expression structure, inlined for
    admission under the same classical convention. Today `$` only marks a
    generated zero-arity relation; it does not certify that inlining preserves
    recursive meaning. Transparency would need an explicit construction contract
    identifying such helpers; a `$` name alone must not authorize it.

  Authored relations, including named DSL terms, remain real boundaries either way;
  document that for DSL authors.
- Exported DSL libraries can show singleton-variable warnings that the user cannot act
  on; print singletons as `_` or skip style lints on generated/library files.
- Each Go to Origin and rename request rebuilds snapshots and reloads programs
  synchronously. Origin restoration indexes current-document ranges and converts
  upstream coordinates in one pass per source; measure the remaining reload cost on
  real programs before adding caches.
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

## `.den` scorecard support — implemented

`just score-den ROOT [--edit ROOT] [--json FILE]` re-scores the provisional
[checker policies](checker-policies.md#re-scoring) on real programs, per verification.
It reports checker phases, size, BDD accounting, outcomes and cache reuse, with fresh
controls and keyed comparisons. Use the measurements to assess the policies below;
private results stay with their programs. Diagnostic quality stays with `check-den`.

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
- **Alternative: completion plus loop formulas** (Lin and Zhao). Clark completion
  already backs the no-meaning check; adding a loop formula for each positive loop
  makes the propositional models exactly the stable models. With BDDs, "exactly one
  stable model in this world" is a quantified query, so admission would be exact
  (necessary and sufficient), not only sufficient. A component can have
  exponentially many loops; elementary loops or lazily added loop formulas, as in
  SAT-based answer-set solvers, are the usual mitigations. Compare both approaches
  when this is picked up.
- **Evidence:** per-world certification of an unsupported cycle inside a larger
  example program was slow and hit the wall-clock deadline intermittently, because
  it settles one world at a time. A symbolic method would decide all worlds at once.
- **Trigger:** real programs with unsupported regions that their input guards
  resolve per world but discharge cannot. Prototype on one component and validate
  against the stable-model oracle and certification. Background: approximation
  fixpoint theory (Denecker, Marek, Truszczyński).

## Limits, then a shared-manager BDD backend

Two steps, in this order.

**1. Simplify limits.** `Limits` has ten fields (cancellation, timeout, atoms, rules,
dependencies, work, BDD variables, BDD nodes, BDD tasks, retained condition nodes),
charged at many sites. Keep the discipline: exhaustion is an explicit inconclusive
result with phase and resource, never a hang, a crash or a proof from partial work.
Keep the operational pair, cancellation and deadline. Collapse the logical limits to
one deterministic **work** counter and one **memory** cap, so exhaustion stays
reproducible cold/warm and in CI. Do this on the current backend first, so the
backend swap is measured against a simple, stable limit model. Evidence: a small
unsupported cycle composed with a larger example program finished certification in
about 11 seconds on one run and hit the wall-clock deadline on another; the same
program and limits gave different results.

**2. Shared-manager backend.** `biodivine-lib-bdd` gives every BDD its own node
vector. Nodes are shared within one condition, and a `Condition` shares its whole BDD
by `Arc`, but there is no unique table across conditions and no operation cache
across applies: facts with common sub-functions store and compute them separately,
and equal formulas installed twice are evaluated twice. A shared-manager library
(for example OxiDD) provides a unique table, an apply cache and constant-time
equivalence.

- **Approach:** a time-boxed spike behind the existing `Condition`/`ConditionContext`
  boundary, measured on the test DSL regression programs and a larger example. Check
  memory bounding, cancellation, determinism of results and of the work counter
  (including under parallel operations), witness extraction, variable ordering,
  licence and maintenance.
- **Limits:** the memory cap maps to manager-level storage rather than per-condition
  sizes (see [checker policies](checker-policies.md)).

**Acceptance for both:** default-limit outcomes, witnesses-as-behaviour and
cold/warm agreement unchanged; no node counts, budgets or timings as goldens.

## Small items

- General-assumption contexts use fresh whole-program evaluation. If a real program
  demonstrates unacceptable cost, re-score before adding constraint-aware local cones
  or proving which restrictions permit the existing absent-extension shortcut; see
  [checker policies](checker-policies.md).
- Let library authors mark obligations as offered but not checked by default, to quiet
  per-consumer notices for menu-style libraries.
- Per-verification scope (domains); today every verification uses its program's domains.
- The test DSL editor treats each open file as one program; composing companion `.den`
  files (extra verifications over an export) is unscoped integration work.

- Trim the unused module/file-based analysis in `crates/analysis`, left from an earlier
  editor prototype.
- Include/exclude lists for the CLI's `den.root` folder scan, which currently also
  walks `.git`, `node_modules` and `target`.
