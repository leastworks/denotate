# 10. Use computed values in task conditions

Earlier Shipping News lessons inspect an independently supplied workspace. Here a
task produces a workspace value, a classification reads it, and another task uses
that classification as its guard. The illustrative DSL might say:

```text
task compute_zone:
    shipment.zone = determine_zone(...)

term domestic:
    shipment.zone is "domestic"

task prepare_customs when not domestic:
    shipment.customs_reference = make_reference(...)
    shipment.receipt = maybe_receipt(...)      # may emit no value
```

These snippets explain the model, not a DSL grammar. The example has no parser or
function implementation. It isolates computations in a small library instead of
duplicating the mapping, type and predicate machinery of [steps 1–9](../README.md).
A task is represented by a `Step` constant in this library.
Type-correct scalar result alternatives are supplied by the lowerer; type checking
and argument bindings are left to the earlier patterns.

From the repository root:

```sh
just check-den editors/den/examples/shipping-news/10-computed-values
just edit-den editors/den/examples/shipping-news/10-computed-values
```

Both `shipping::computation_sources` and `shipping_example::valid_shipments` report
`proved`, with exit 0. The three selected notices vary, so they produce no diagnostics.

## Start with what is open

The [library](library/computations.den) has two result inputs:

```den
input step_result(step: Step, element: Element, value: Value) within result_candidate;
input output_emitted(step: Step, element: Element) within conditional_output;
```

`step_result` describes what a task would return if used. It does not assert that the
task has run or that its result is available. `output_emitted` controls whether a
conditional output is emitted. Each required output is emitted whenever its task
applies; it needs no emission bit. Required and conditional outputs are distinct
declaration forms, not different runtime values.

The [consumer](program.den) gives `compute_zone` two possible results, domestic and
international. The reference and receipt each have one abstract result class. In
a fuller abstraction those could stand for many concrete values. Sharing an
abstract marker does not establish equality of concrete results.

The result assumptions select exactly one value per declared output pair, even for
an inactive task or an un-emitted output. Those unused choices have no effect on
workspace availability. Conditional absence is represented by the emission bit,
not a special `nil` value in `step_result`.

## Make availability derived

The central rules are:

```den
writes(S, E) :- step_applies(S), required_output(S, E);
writes(S, E) :- step_applies(S), conditional_output(S, E), output_emitted(S, E);
element_value(E, V) :- writes(S, E), step_result(S, E, V);
element_present(E) :- element_value(E, _);
```

`writes` describes an emitted output in this model. It is not an execution event
log. An inactive task supplies no workspace value, even though its guessed result
exists. In particular, the receipt is absent on domestic shipments even when its
emission input is true.

The consumer lowers classification and its guard to rules:

```den
step_applies(compute_zone);
classified(term_ids::domestic) :- element_value(shipment::zone, literals::domestic);
relation $not_domestic();
$not_domestic() :- !classified(term_ids::domestic);
step_applies(prepare_customs) :- $not_domestic();
```

For domestic results, the customs task does not apply. For international results,
it supplies the reference and may supply the receipt. The library checks at most
one writer per element; consumer obligations check that customs references are
present for international shipments and absent for domestic ones.

**Try an edit:** change the reference's `required_output` declaration in
`program.den` to `conditional_output`. The reference can now be omitted, and
`no_missing_customs_reference` fails (exit 1). Restore `required_output` to clear it.
The receipt remains conditional throughout.

## Follow the concrete dependencies

Reading only predicate names suggests a negative cycle. Arrows below mean
“depends on”:

```text
step_applies → $not_domestic → !classified → element_value → writes → step_applies
```

But the grounded dependencies for this consumer form a chain:

```text
step_applies(prepare_customs)
    depends on NOT classified(domestic)
    depends on element_value(zone, domestic)
    depends on writes(compute_zone, zone)
    depends on step_applies(compute_zone), an unconditional fact
```

Nothing here reads back from the customs outputs. No ground negative cycle needs
admission or a redundancy rewrite. This is the reason the library can use generic
predicates for every task without splitting them by execution stage.

The consumer also declares `valid_message`: an international shipment must include
customs details. Its constraint reads the computed classification. Its cycle between
relation names defers validation from loading to the checker, which establishes that
its ground cone has no negative cycle, independently of any selected assumption.
It can therefore be selected by `valid_shipments`. Loading alone would not prove
this validity.

There are 8 worlds satisfying the result contracts. `valid_message` excludes the
2 international worlds without customs details, leaving 6. Both domestic and
international shipments remain possible. `computation_sources` deliberately checks
all 8 worlds; no validity assumption activates implicitly.

## Require results only for declared outputs

There are two steps and three elements, but only three output pairs. Writing
`exactly_one(step_result, group_by: (step, element))` would require results for all
six pairs in the sort product and make this example inconsistent.

The library expresses sparse coverage using existing vocabulary:

```den
result_present(S, E) :- step_result(S, E, _);
missing_result(S, E) :- step_output(S, E), !result_present(S, E);
assumption every_output_has_result: empty(missing_result);
assumption at_most_one_result: at_most_one(step_result, group_by: (step, element));
```

The coverage assumption follows declared outputs. The uniqueness assumption can
still use the full grouping domain: a nonexistent pair cannot have two results.
Both constraints depend only on result inputs and fixed metadata, never on task
applicability or the resulting workspace.

**Try an edit:** remove the reference's `result_choice` fact. Its output declaration
still requires a result but has no eligible candidate. Both verifications report
`inconsistent-assumptions` (exit 1); an empty candidate set does not hide the output.
Restore the fact to repair the program.

## Exercises: when the chain really closes

Each exercise is a separate root that shares this lesson's small library.

```sh
just check-den editors/den/examples/shipping-news/10-computed-values/exercises/self-support
just check-den editors/den/examples/shipping-news/10-computed-values/exercises/negative-cycle
```

In [self-support](exercises/self-support/program.den), a task needs the classification
that reads its own output. The result input is present, but no rule starts the task.
At the least fixed point the task, value and classification are all absent. Its
notice is `impossible-condition`; exit is 0 because notices are advisory.

**Repair:** replace `step_applies(assess) :- $ready();` with
`step_applies(assess);`. This gives the computation an independent start. The notice
becomes `always-true-condition`. Consistency of a hypothetical self-supporting
answer was never sufficient to supply that start.

In [negative-cycle](exercises/negative-cycle/program.den), the task instead requires
its classification to be false. Applying produces the value that makes the
classification true and disables the task. Not applying leaves the classification
false and requires the task to apply. The checker reports `no-meaning` and exits 1;
the notice is `unknown`, reported as `unanalysed-condition`, not impossible.

The `no-meaning` diagnostic also shows the concrete dependency cycle through
`classified(loop::ready)`, `element_value(loop::zone, loop::domestic)`,
`writes(loop::assess, loop::zone)`, `step_applies(loop::assess)` and `$not_ready()`.
Arrows mean “depends on”; `-not->` marks the negative dependency. This retained
structural path is separate from the example input observation that demonstrates
the inconsistency. Other cycles can have consistent equations and still be unsupported.

**Repair:** replace `step_applies(assess) :- $not_ready();` with
`step_applies(assess);`. The task then always applies, while `$not_ready` is always
false. The notice becomes impossible and exit returns to 0.

**Probe the assumption boundary:** before repairing the negative cycle, add the
following declarations inside its `namespace loop`:

```den
relation invalid_message();
invalid_message() :- !classified(ready);
assumption valid_message: empty(invalid_message);
```

This produces `invalid-assumption`, even without selecting it: its ground cone
really is cyclic. Unlike the main lesson's validity assumption, it has no
independent stratified meaning. Another assumption cannot hide that cycle.

## What this lesson does and does not establish

The model derives availability from abstract results in each complete input world.
It does not execute UDFs, prove their contracts, or schedule calls. In particular:

- Guessed results are independent unless explicit contracts relate them. Real pure
  functions can correlate results more strongly; this model can expose possibilities
  their implementations never produce. It also does not correlate repeated runs.
- “Not yet computed” is different from “known absent.” A runtime cannot fire the
  negative customs guard merely because the zone computation has not finished.
  The example checks final relational meaning, not intermediate runtime snapshots.
- General recursive programs can be unsupported or inconclusive. A genuine negative
  cycle is not guaranteed to be contradictory like this exercise: some have consistent
  equations without established meaning. Ordinary admission and certification keep
  their existing rules; assumptions require independent ground stratification.
- The small model makes no scalability claim for thousands of tasks. Re-score an
  exported real program with `just score-den` before drawing performance conclusions.

**Denotate concepts learned:** Separate open outcomes from derived availability;
ground task identities can break cycles between generic predicates. Sparse coverage
can be stated with `empty` over missing declarations. Positive self-support needs
an independent base, and negation cannot turn a contradictory cycle into a proof.
