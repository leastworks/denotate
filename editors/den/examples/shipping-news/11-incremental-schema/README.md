# 11. Decide which message fields belong to the schema

This advanced example is the incremental-schema lesson's runnable kernel. It
models a compiler's growing knowledge explicitly, using ordinary `.den` relations.
It has no parser, scheduler, SAT-derived lemmas or changes to Denotate's semantics.

```sh
just check-den editors/den/examples/shipping-news/11-incremental-schema
just edit-den editors/den/examples/shipping-news/11-incremental-schema
just test-shipping-news
```

Both verifications prove at default limits; exit is 0. The knowledge program is
admitted without cyclic rewrites. Larger split limits give the same result.
The separate [loop cases](#small-programs-to-compare) include deliberate unresolved
decisions and return exit 1 where documented below.

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
was supplied. Its value test waits for that source decision before reading the raw input.
An expectation conditional on an ancestor, such as Booking Request's optional
note, is static for the leaves below that ancestor.

### Field tests wait for readiness

The `reads(test, accepted, observation)` gate has a different rule from AND:

| Acceptance | Test result |
| --- | --- |
| Known true | The raw observation's truth value |
| Known false | False: the workspace slot is unset |
| Undetermined | Undetermined, even if the raw observation is false |

Equality and presence use this gate. Inequality and absence negate the resulting
knowledge flags, so `is not 0` includes a known absent value. A raw absence must not
start a circular acceptance decision: the modeled runtime cannot inspect a field
before deciding whether it belongs to the workspace. Raw observations are internal
lowering inputs, never an alternative interpretation of a DSL guard.

Boolean AND/OR retain their rules above. An independently false guard can therefore
make a writer inapplicable even while another operand is unknown. Computation
results similarly remain unreadable until applicability is known.

### Conditional expectations and validation

For a non-ancestor guard, `expected_when(leaf, field, guard)` uses the **disjunction
of every declaration giving that field in that leaf**. Coverage holds when this
guard is known true or the leaf is excluded. A matched leaf whose aggregate guard
is known false establishes that the field is not accepted. The lowerer must supply
the complete guard, including an explicit false constant when nothing gives the
field. Static `expected` / `not_expected` facts are the unconditional alternative.

Keep three stages separate:

1. Match or exclude structural paths using their terms. Coverage reads this stage.
2. Validate the matched leaf's original guarded declarations. A required value
   missing from the workspace gives `missing_field`; a declared-absent value that
   is present gives `forbidden_field`. `required_field` and `absent_field` each
   produce a failure decision with both true and false knowledge.
3. Recognize a message when a path matches and validation is known to pass.

Validation never feeds matching or exclusion. Otherwise a leaf that matches
unless its required field is missing can become stuck instead of rejecting the
message. A dropped, unexpected incoming value is not a validation failure.
Field ownership and validation are separate catalogs: an absence constraint can
validate an owned slot, without contributing another source for it.

### Lift exhaustive giving guards, preserve their validation

Consider this illustrative declaration:

```text
when fee is not 0: fee required
when fee is 0:     fee optional
```

The giving guards cover every value, including absence. The lowerer can emit
unconditional `expected(leaf, fee)` for ownership. It **keeps** the first guard for
required-field validation: an absent fee is accepted as a slot, then rejected as
missing. Swapping required and optional makes absence valid instead.

This is a DSL lowering rule, not a Denotate rewrite or an assumed obligation. The
handwritten examples demonstrate its result; they do not implement a formula
compiler. The rule is limited to guards using this field's comparisons, presence
and Boolean operators, with validity checked across its complete value domain,
absence included. An independent guard cannot be discarded: `(G and fee = 0) or
(G and fee != 0)` still depends on G. Without the lift, the circular strict reads
remain undetermined in every world.

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
these rejected messages. The separate cases below add guarded validation.

## Small programs to compare

Each case has its own root and uses the same knowledge library. Run one by replacing
the final directory in this command with a linked case name:

```sh
just check-den editors/den/examples/shipping-news/11-incremental-schema/cases/k1-exhaustive-guards
just check-den editors/den/examples/shipping-news/11-incremental-schema/cases/w1-self-reading-set
```

The first command proves (exit 0); the second reports `no_unknown_decisions`
(exit 1). Both knowledge programs are admitted without cyclic rewrites. Every
case checks **all** permitted inputs, without a recognition assumption. Required
computation outputs use lesson 10's open-result convention: one abstract result
per output even while inactive. W2/W4 have the single result `1`; an inactive
computation still leaves `a` absent.

The following comparison distinguishes the knowledge translation from a direct
stable-model lowering of the source rules. The completion column describes a
scheduler that requires the rules' completion to decide each loop, treating a
message with no completion model as invalid; it is an illustrative approach, not
part of this repository. The runnable cases and exhaustive tests verify the
knowledge column. A direct-lowering comparison suite is deferred.

| Case and source rule | Completion-based scheduler | Direct stable-model lowering | Knowledge form / CLI exit |
| --- | --- | --- | --- |
| [W1](cases/w1-self-reading-set/): `when a present and g = 1 => set a = 1` | Rejects two completion models when g = 1 | Writer never fires | Writer unknown when g = 1; otherwise known inactive / **1** |
| [W2](cases/w2-self-reading-computation/): W1 with a computation | As W1 | As W1 | As W1 / **1** |
| [W3](cases/w3-self-negating-set/): `when a absent and g = 1 => set a = 1` | Silently treats g = 1 as invalid | No meaning when g = 1 | Writer unknown when g = 1; otherwise known inactive / **1** |
| [W4](cases/w4-self-negating-computation/): W3 with a computation | As W3 | As W3 | As W3 / **1** |
| [k1](cases/k1-exhaustive-guards/): fee != 0 required; fee = 0 optional | Accepts fee by exhaustive guards | No meaning for fee = 0 | Lift accepts fee; absence is a known missing-value rejection / **0** |
| [k2](cases/k2-self-reading-expectation/): fee present ⇒ fee required | Rejects ambiguity | Fee stays dropped | Acceptance unknown, including absent input / **1** |
| [k3](cases/k3-self-negating-expectation/): fee absent ⇒ fee required | Fails on the contradictory case | Missing-value rejection or no meaning | Acceptance unknown in every world / **1** |
| [k3b](cases/k3b-conditional-expectation/): fee absent and g = 1 ⇒ fee required | Can silently discard the missing-value rejection | Rejects absent fee; no meaning with fee, under g = 1 | Unknown when g = 1; otherwise fee dropped and message recognized / **1** |
| [k4](cases/k4-partial-classification/): A reads kind r; B reads kind s and f = 10; B supplies f | Selector excludes A, unlocking f | B cannot start through its own supplied field | Same partial classification as compiler / **0** |
| [k5](cases/k5-every-leaf-supplies/): k4, A also supplies f | Accepts f unconditionally | B still cannot start | Every leaf supplies f / **0** |

Two controls isolate the k1 rule: [without the lift](cases/k1u-without-lift/), fee
acceptance stays unknown for every input (exit **1**); [swapping validation kinds](cases/k1s-swapped-validation/)
still accepts fee in every world, but an absent fee is optional and recognized
(exit **0**). In k4/k5, kind s with f absent or 20 fails classification, not a
required-field check: B never matches. Missing kind also fails classification.

Strict readiness deliberately differs from inferring workspace absence directly
from raw absence. That is why k2/k3/k3b can remain unknown even when the message
carries no fee. Neither the knowledge encoding nor its audit silently filters
these worlds. It also does not implement the direct stable-model writer result:
self-reading writers remain unknown instead of being assigned false.

The twelve programs cover 54 permitted input worlds (92 Boolean assignments
before scalar/result restrictions). Tests compare every declared decision's flags
with an independent per-message reference, check the documented world outcomes,
and compare cold/warm sessions, including repairing and restoring k3b. Additional
checks exercise declared-absent validation. Recognition being known false is a
modeled message rejection, not an authoring error: the CLI proves decision
completeness, not that every input message must be recognized.

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
