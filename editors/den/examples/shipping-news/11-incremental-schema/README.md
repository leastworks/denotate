# 11. Decide which message fields belong to the schema

This advanced example is the first part of the incremental-schema lesson. It
models a compiler's growing knowledge explicitly, using ordinary `.den` relations.
It has no parser, scheduler, SAT-derived lemmas or changes to Denotate's semantics.

```sh
just check-den editors/den/examples/shipping-news/11-incremental-schema
just edit-den editors/den/examples/shipping-news/11-incremental-schema
just test-shipping-news
```

Both verifications prove at default limits; exit is 0. The knowledge program is
admitted without cyclic rewrites. Larger split limits give the same result.

## The feature being lowered

An illustrative schema has two message types, each with two directions:

```text
Booking                         Cancellation
  Request                         Request
  Response                        Response

every leaf: direction from the message
every Request leaf: request_kind from the message
every Response leaf: response_kind from the message
when Booking and Request: note optional from the message

when Request and request_kind is booking: set category = booking
when Request and request_kind is cancellation: set category = cancellation
when Response and response_kind is booking: set category = booking
when Response and response_kind is cancellation: set category = cancellation

Booking means category is booking
Cancellation means category is cancellation
fallback guard: not Booking and note is absent
```

Each input field is absent or has one value from its finite candidate set. Values
are abstract literals; there are no UDF results in this example. The `category`
value comes from the set statements. Two statements producing the same value are
allowed. Different values conflict, and a set cannot write a message-owned field,
even when its optional raw value is absent.

The circular-looking part is intentional: the selected format determines which
fields belong to the message, but classification reads values computed from those
fields. Partial classification breaks the cycle:

1. Every leaf supplies `direction`, so it can be read immediately.
2. A Request excludes both Response leaves, before Booking or Cancellation is known.
3. Every remaining leaf supplies `request_kind`, so that field can be read.
4. The matching set statement computes `category`, which determines the root.
5. The remaining acceptance decisions settle. A supplied `note` on a Cancellation
   message is discarded; it cannot make `note is absent` false.

## Represent knowledge, including known absence

[The library](library/knowledge.den) uses two atoms for each decision:

| `known_true(D)` | `known_false(D)` | Meaning |
| --- | --- | --- |
| present | absent | Known true |
| absent | present | Known false |
| absent | absent | Undetermined |
| present | present | Conflicting knowledge: a lowering error |

For an AND, true requires both inputs true; false needs either input false. For an
OR, true needs either input true; false requires both inputs false. Negation swaps
the two flags. Thus `not Booking` reads Booking's **known-false** flag, never the
absence of its known-true flag. Multiple producers are combined by OR; false must
account for every producer. The lowerer emits an explicit false constant for a
decision with no producers.

[The program](program.den) spells these operations as finite gate facts. These are
a sample lowering convention, not a new Denotate language feature. The category
tests combine the guards of all statements writing that literal; `set_value` also
records the resulting values for the write-conflict obligations. A real lowerer
must keep those producer lists and output declarations in agreement.

Coverage follows the same approach. A leaf is covered for field F if it declares
F message-supplied or is known excluded. The binary tree combines the coverage
of every leaf. A field's source is then known independently of whether a raw value
was supplied. Its value test combines that source decision with the raw input.
An expectation conditional on an ancestor, such as Booking Request's optional
note, is static for the leaves below that ancestor.

The decision rules negate only raw inputs. All recursive dependencies between
knowledge atoms are positive. Denotate therefore evaluates their ordinary least
fixpoint, also the unique stable model of **this knowledge program**. No completion
or proof that a negative cycle is harmless is needed. The final unknown-decision
report uses negation of knowledge flags, but never feeds back into propagation.

## Admission does not imply that every decision became known

The independent test reference uses three-valued Kripke–Kleene propagation. It
starts derived decisions as undetermined and applies the equations until knowledge
stops growing. The tests compare both flags for every decision across all 54 scalar
input worlds (128 assignments before the scalar restriction); 24 are recognized.

This reference is deliberately weaker than well-founded reasoning. For the source
equation `p :- p`, the knowledge translation has `p_true :- p_true` and
`p_false :- p_false`. Neither flag starts: p stays undetermined. The original
positive program, in contrast, has p false at its least fixpoint. Similarly,
propagation cannot establish `T or not T` when T itself is undetermined. The sample
does not add a fact or rewrite a rule to bridge that gap.

The unfiltered `schema::propagation` verification selects only the scalar-input
assumption. It requires recognition, the field-source decisions, the terms used
by guards and every set's applicability to become known, and checks knowledge
consistency, path overlap and writes. This is where an inability to derive a flow
must remain visible.

`schema::recognized_messages` additionally selects `recognized_message`. That
assumption is valid because its dependency cone has no negative cycle. It restricts
worlds to those whose recognition flag is **known true**; it does not prove that
recognition is decided in every scalar world. The path-overlap obligation is
checked in the unfiltered verification, before this restriction.

A known-false recognition result is a classification rejection, not an unknown
decision. When all leaves are excluded, field coverage is vacuously true; the
message is still rejected. The example makes no runtime acceptance promise for
these rejected messages. Required-field validation and declared-absent constraints
are left for the rest of the lesson.

**Try an edit:** replace

```den
both(set_request_booking, request, request_booking);
```

with

```den
const circular_booking_guard: Decision;
both(circular_booking_guard, request, request_booking);
both(set_request_booking, circular_booking_guard, booking);
```

The Booking writer now needs its own computed classification. The knowledge
program is still admitted, but `no_unknown_decisions` fails in `propagation`
(exit 1). The recognized-only verification still proves: it has filtered out the
undecided requests. Restore the original guard to repair the flow. Tests cover
this repair with cold and warm sessions.

**Denotate concepts learned:** Positive recursion can represent partial knowledge
without making an unresolved fact false. Keep admission, decision completeness
and input-world selection separate, and validate the lowering with an independent
per-message reference.

[Back to Shipping News](../README.md)
