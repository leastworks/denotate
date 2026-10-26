# denotate-check

The finite relational checker. It grounds a `Corpus` over explicit finite domains,
checks admissibility, replays concrete input worlds, and proves or refutes
`at_most_one` and `at_least_one` obligations symbolically (BDD by default, SAT selectable), returning
only replayed counterexamples. Runtime dependencies: `denotate-ir`, pinned
`biodivine-lib-bdd` and a pinned SAT solver.

## Pipeline

1. **Domains.** `Domains` maps every sort to its typed constants. The checker never
   infers domains from rules; constants used by rules must be in their domain. Empty
   domains are allowed.
2. **Preparation.** `GroundProgram::prepare` computes possible atoms and rule
   instances and builds provider-first ground components, keeping original rule, atom
   and argument occurrence IDs. `prepare_with_input_groups` adds input assumptions W
   (`InputAtMostOne` on input relations): permitted worlds have at most one tuple per
   group. `admit` applies justified rewrites.
3. **Admissibility.** Positive cycles are admitted. A negative edge inside an SCC blocks
   that component and its dependents unless a rewrite proves the negation redundant
   under W. Blocked regions are reported (`Unsupported`), never treated as false.
4. **Concrete replay.** `evaluate(present_inputs)` runs admitted components on a
   complete input snapshot (omitted tuples are absent; observations violating W are
   rejected). Facts are `Settled(true|false)` or `Blocked`; each established fact keeps
   its first grounded derivation; absence evidence names its provider component, the
   input snapshot or `NoPossibleProducer`.
5. **Symbolic meaning.** `symbolic` computes a condition per fact over the input
   variables; `check_at_most_one` gives scoped group results: `Proved`,
   `Overlap(condition)`, `Unsupported` or `Inconclusive { phase, resource }`.
6. **Verification.** `verify_at_most_one` turns overlaps into `Counterexample`s only
   after concrete replay confirms at least two distinct tuples. Findings carry the
   complete observation, the grounded proof DAG and the replay scope (`WholeProgram`,
   or `ConeOnly` when the whole program is not admitted).
7. **Certification.** `certify_observation` can establish one world's meaning in an
   otherwise unsupported program, upgrading `ConeOnly` replay for that observation.
8. **No-meaning findings.** For remaining negative-cycle components, completed
   equations identify permitted inputs with no consistent result. This is a sufficient
   failure check, not admission: a consistent equation solution does not establish
   meaning.

Reporting callers use the `*_checked` entry points: exhaustion before a report exists
is a top-level inconclusive outcome, never an empty success.

## Requests, keys and results

`CheckRequest::for_verification` builds a request from one IR verification: only its
selected assumptions constrain permitted worlds, and only its selected obligations
produce groups (including the compact domains for trivial groups). Preparation
rejects unknown obligation or verification keys and requests whose constraints or
obligations do not match their named verification. Current input `at_most_one`
assumptions are jointly consistent because they permit all inputs to be absent.

Admission, rewrite proofs and no-meaning/unsupported analysis use that request's
constraints even when no obligations are selected. Unselected assumptions have no
effect. The transitional `all_obligations` constructor keeps existing callers working
with `verification: None`; unnamed requests may also select an obligation subset.
The public `GroundProgram::prepare*` entry points still cover all obligations.

`ScopedResults.context` retains the request, including its optional `VerificationKey`.
Per-group and per-region outcomes use semantic identities (`GroupKey`, `ComponentKey`,
`AtomKey`), so results correspond across snapshots without arena IDs. Witness ordering
follows canonical `AtomKey` order, independent of declaration order.

Sessions share join plans and possible-tuple grounding independently of verification
selection. Group construction and admission run for the current request. Cached local
answers include their relevant constraints, input groups and obligation shape;
completion also includes any discharge-proof context. The result's request context
and counterexample replay are assembled fresh, so reused work cannot carry a previous
verification's identity into the current result.

## Coverage

`Verification.coverage` and `ScopedResults.coverage` contain per-obligation summaries:
examined groups, missing groups, unsupported groups, an optional inconclusive reason,
zero-group status and at most three replayed examples. Missing counts are exact only
when `complete()` is true. `proved()` requires complete checking and zero missing groups.
`ScopedResults::group` does not infer coverage from zero/one possible tuples: use the
coverage summary for its outcome. Existing uniqueness group identities are unchanged.

Coverage streams the Cartesian product of resolved grouping domains under a per-obligation
work allowance; retained examples are bounded independently. Empty grouping has one
group; an empty grouping-column domain has none. Counterexamples require replay-confirmed
absence of all possible members. When replay is blocked, observation certification may
establish absence or presence; uncertified worlds remain unsupported while bounded search
continues for a settled counterexample. A known-present tuple can prove coverage without
settling other producers. All-absent inputs witness consistency of the current assumptions.

Both coverage backends currently share symbolic fixed-point evaluation. BDD searches the
resulting absence condition; SAT encodes that condition as a Boolean circuit and solves it,
then both replay the concrete observation. SAT coverage therefore shares BDD evaluation
limits; it does not yet provide an alternative for programs that exhaust BDD evaluation.
The existing SAT uniqueness implementation is unchanged. Sessions reuse preparation but
recompute coverage evaluation and summaries each check; a separate coverage verdict cache
is deferred until measurements justify it. These choices affect performance/inconclusiveness,
not the meaning of conclusive answers.

## Rewrites

Conservative rewrites remove a literal or rule only with a proof (for example, a
negation that is redundant under the other premises and W). They are reported as
rewrite findings with their coverage; they never authorize source edits.

## Limits and cancellation

`Limits` bounds atoms, rule instances, dependencies, work, BDD storage and elapsed
time; exhaustion yields explicit inconclusive outcomes with phase and resource.
`Cancellation` is cooperative and checked at phase boundaries.

## Tests

```sh
cargo +1.93.0 test --locked -p denotate-check
```

Tests include independent oracles: a Cartesian-grounded stable-model oracle for
rewrites and grounding, exhaustive small-world comparisons, and portable-condition
regression tests.
