# denotate-check

The finite relational checker. It grounds a `Corpus` over explicit finite domains,
checks admissibility, replays concrete input worlds, and proves or refutes
`at_most_one`, `at_least_one`, `exactly_one` and `empty` obligations symbolically (BDD), returning
only replayed counterexamples. Runtime dependencies: `denotate-ir`, pinned
`biodivine-lib-bdd`.

## Pipeline

1. **Domains.** `Domains` maps every sort to its typed constants. The checker never
   infers domains from rules; constants used by rules must be in their domain. Empty
   domains are allowed. An input's optional `within` provider is evaluated exactly
   over its input-free, stratified cone before input atoms are seeded. This shares
   preparation limits and fails all-or-nothing with phase `input domains`. Grounding
   uses the complete eligible tuple set; coverage still uses the sort domains.
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
   It still requires the whole program to complete. Emptiness and coverage searches
   skip worlds equivalent on all target and certification dependencies, preserving
   unresolved outcomes; see [checker policies](../../docs/checker-policies.md#certification-search).
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
obligations do not match their named verification. Input-only `at_most_one` contexts
retain their local checking path. General input/derived cardinality constraints
compute W independently during preparation, then use whole-program checking.
An empty W reports `inconsistent_assumptions` with no obligation results. Unknown W
is inconclusive. The IR classifies constraint cones before this evaluation; selected
cones requiring grounding must have no reachable negative cycle in the raw graph.

`validate_assumption_cones(corpus, domains, keys, limits)` is the program-level
declaration query, called before verification loops, including when none exist. It
uses relation-stratified cones immediately; others use fresh unrestricted grounding
with no obligation groups, followed by the existing graph's `blocked_by` and cycle
evidence. Results identify assumptions and cycle edges with semantic keys. It never
uses selected assumptions or admission, and never rejects an unrelated ground cycle.
An exhausted query retains established results and marks remaining declarations
inconclusive; cancellation aborts. The query currently recomputes, so facts, domains
and input eligibility cannot leave stale validation. Request preparation also checks
selected restrictions, including unnamed API requests, before computing W, returning
`InvalidAssumptionCone` with keyed evidence on failure. Program-level invalid
declarations do not prevent unrelated verifications from preparing.

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
settling other producers. Selected assumptions must be consistent before coverage runs.

Coverage uses symbolic BDD fixed-point evaluation and searches the resulting absence
condition, then replays the concrete observation. Sessions reuse preparation but
recompute coverage evaluation and summaries each check; a separate coverage verdict cache
is deferred until measurements justify it. BDD is the only backend; the retirement and
reintroduction criteria are in [checker policies](../../docs/checker-policies.md#backend-retirement).

## Exactly one

An exactly-one obligation contributes its domain factors to coverage and its possible
multi-tuple groups to uniqueness. Both use the same selected input assumptions; neither
result is used as a restriction for the other. The existing evaluation, replay, budgets
and caches implement each part without a second authored obligation.

`ScopedResults.coverage` retains the coverage summary and `groups` retains uniqueness
results under the same obligation key. `KeyedGroups.kind` identifies the authored form;
`ScopedResults::group` queries uniqueness for exactly-one, not the combined obligation.
The overall verification proves only when both parts prove (and context-wide checks
succeed). An established failure survives exhaustion of the other part; both outcomes
remain available. The fresh global and cached local paths follow the same rule.

## Rewrites

Conservative rewrites remove a literal or rule only with a proof (for example, a
negation that is redundant under the other premises and W). They are reported as
rewrite findings with their coverage; they never authorize source edits.

## Limits and cancellation

`Limits` bounds atoms, rule instances, dependencies, work, BDD storage and elapsed
time; exhaustion yields explicit inconclusive outcomes with phase and resource.
`CheckError`, `Inconclusive` and keyed `ResourceReason` carry `LimitDetails`: optional
subphase, effective limit and observed demand at the failed check. Observed demand
may include a rejected addition; an unknown solver count remains absent. Deadlines
carry the allowance in milliseconds, never elapsed timing. Input-domain preparation
preserves provider discovery/grounding/analysis/evaluation versus input enumeration.
Details do not charge work or alter verdicts; forwarded and cached reasons retain
them. Backend capacity or available work/storage can tighten the effective ceiling.
`Cancellation` is cooperative and checked at phase boundaries.

## Tests

```sh
just test-crate denotate-check
```

Tests include independent oracles: a Cartesian-grounded stable-model oracle for
rewrites and grounding, exhaustive small-world comparisons, and portable-condition
regression tests.

## Emptiness

`empty` has one ungrouped `EmptinessReport` per selected obligation (keyed as
`EmptinessResult` in `ScopedResults.emptiness`). `examples` defaults to at most three
distinct replayed present tuples, each with its own observation.
`PreparedCheck::with_emptiness_examples(EmptinessExamples::Limited(n))` selects a
positive sample size; `EmptinessExamples::All` retains every confirmed tuple.
This invocation-level reporting choice is outside `CheckRequest`, semantic limits
and cached inputs. It changes neither candidate enumeration nor deterministic
charges. Extra examples consume memory and receive independent post-check attribution
allowances. All modes keep semantic-key order and exact/lower-bound count semantics.
`unresolved` and `inconclusive` keep unknown
worlds and resource exhaustion visible independently of a known failure. `proved()`
requires complete analysis and zero present tuples. The BDD checks settled presence conditions;
blocked facts require world replay/certification, with enumeration and evidence charged
to the obligation's allowance. Sessions reuse preparation and recompute these verdicts.

## Advisory condition queries

`Corpus::notice_varies_in` declares a zero-arity condition and optional enclosing
scope; `verification_with_notices_in` selects notices. `CheckRequest::for_verification`
validates and retains that selection. `ScopedResults.notices` returns keyed results.
`GroundProgram::analyze_condition` is the corresponding low-level query on a prepared,
admitted program: impossible, always true, varying, parent unreachable, or unknown.
The query uses W, symbolic settled conditions and independent concrete replays; it
never assumes the conclusion. Both sides of varying have their own full observation.
Unknown results retain the cause: `ConditionAnalysis.blocked_by` records the blocking
components returned by symbolic meaning; `NoticeResult.blockers` projects these to
semantic component and cycle-rule keys for presentation. Deadline reasons retain the
phase. Collecting this evidence does not perform additional checking or charge budgets.

Each selected notice runs after ordinary checking with a fresh deterministic and
operational allowance. Its receipts use `QueryKey::Notice`; a deadline is unknown
without a semantic receipt, while cancellation aborts. Sessions currently recompute
these queries. They do not affect obligation verdicts/completeness. No implicit
notice selection is added to the legacy `all_obligations` constructor.
