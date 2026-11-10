# Shipping News: a DSL on Denotate

Shipping News is an **illustrative** language for translating carrier messages into
a canonical shipment record, classifying that record, and preparing outbound labels.
There is no Shipping News parser or UDF runtime. The runnable `.den` files are
handwritten examples of what a lowerer would emit. The `text` snippets below explain
the intended authoring language; they do not specify a grammar.

Start with a carrier's `mass` and `destination` fields and the business concepts
`shipment.weight` and `shipment.country`. Then add conditional routes, conversions,
optional flags, external predicates and classifications. Each step is a complete
program with its own library. Steps 1–9 retain the features and repair the deliberate
errors in earlier ones. [09-complete](09-complete/) is the complete mapping sample.
[Lesson 10](10-computed-values/README.md) adds a focused computation model: task results
become workspace values, classification reads them, and classifications guard other tasks.
Each lesson builds a DSL feature and ends with a brief recap of the Denotate concepts
used to support it.

From the repository root:

```sh
just check-den editors/den/examples/shipping-news/01-declarations
just check-den editors/den/examples/shipping-news/09-complete
just edit-den editors/den/examples/shipping-news/09-complete
```

Each root's `den.root` includes `library/den.root`. That is program membership;
`use shipping;` only makes names visible. A `namespace` is a naming scope, not a
file or a separately executed module. The consumer files hold the **program facts**
a lowerer would emit for one Shipping News program. Carrier and shipment values are
**runtime inputs** in steps 1–9, which vary between worlds
([terms](../../../../docs/den-format.md#terms)). Lesson 10 instead derives workspace
values from task applicability and open result inputs.
Library verifications run over the consumer's facts. Their diagnostic locations can
therefore point into the consumer.

Output excerpts below omit absolute paths, repeated locations and unrelated proved
verifications. Exact wording and selected examples may evolve; the tests assert
outcomes, finding kinds, notice states and relevant placement, not rendered goldens.

| Step | Expected outcome | CLI exit |
| --- | --- | ---: |
| [01 — Declare typed fields and shipment elements](01-declarations/) | One field lacks a type; one coverage finding | 1 |
| [02 — Validate direct mappings](02-direct-mappings/) | One invalid mapping; one emptiness finding | 1 |
| [03 — Detect conflicting conditional mappings](03-guards/) | Two routes overlap; one uniqueness finding at both routes | 1 |
| [04 — Support conversion functions](04-converters/) | All four verifications proved | 0 |
| [05 — Add feature toggles and optional flags](05-toggles-and-flags/) | All four verifications proved | 0 |
| [06 — Support predicate functions and their contracts](06-check-contracts/) | All five verifications proved under their selections | 0 |
| [07 — Define reusable classification terms](07-classifications/) | All five verifications proved | 0 |
| [08 — Help authors understand their conditions](08-condition-notices/) | All six proved; one always-true and one impossible notice | 0 |
| [09 — Review what the completed library guarantees](09-complete/) | Same results as step 08; understand the model's limits | 0 |
| [10 — Use computed values in task conditions](10-computed-values/README.md) | Both verifications proved; all three notices vary | 0 |

There is no claim that every destination must have a mapping. The mapping contract
is **at most one applicable writer**, not coverage of all destinations.

The Shipping News library uses `snake_case` property names for obligations, with
explicit cardinality where it matters: `exactly_one_type_per_field`,
`at_most_one_inbound_source`, and `no_invalid_mappings`. For `empty(...)`
obligations, `no_<violations>` names what must be absent: for example,
`no_invalid_field_comparisons: empty(invalid_field_comparison)`. The relation names
the violations; the obligation requires their absence. Notices name the guard use
and the question, such as `nested_customs_guard_varies`, so their names remain valid
when the result changes. The declaration keywords already distinguish requirements
from advisory queries; names do not add `must` or `should`. This is a convention for
this sample, not a Denotate naming rule.

## 1. Declare typed fields and shipment elements

Illustrative declarations:

```text
message Carrier:
    mass: Number
    destination                 # missing type
shipment:
    weight: Number
    country: Text
```

The [library](01-declarations/library/types.den) defines one `DataType` sort with
`number` and `text` constants. A new business data type does not require a new
family of relations. `Field` and `Element` identify distinct kinds of endpoints.
The [consumer](01-declarations/declarations.den) declares the actual endpoints:

```den
namespace carrier {
    const mass, destination: shipping::Field;
    shipping::field_type(mass, shipping::number);
}
```

The standard library contract is:

```den
obligation exactly_one_type_per_field: exactly_one(field_type, group_by: field);
```

Every field in the program's resolved domain needs one type. `exactly_one` checks
coverage and uniqueness independently. An author who supplies two types gets a
uniqueness failure; no annotation produces a coverage failure.

```text
declarations.den:3:17: counterexample: Obligation exactly_one_type_per_field (coverage): 1 group fails coverage.
  note: Missing group (carrier::destination).
Result: findings
```

The primary is the consumer's `destination` constant, not the library obligation.
Uncomment `field_type(destination, text);` to clear the finding. Step 02 already
contains that repair. The library by itself has empty endpoint domains and may
show Information notes about empty grouping domains; that is distinct from checking
a consumer with declared fields.

**Denotate concepts learned:** Sorts, constants and facts describe the DSL model;
`exactly_one` checks both coverage and uniqueness, with missing-group findings placed
on the consumer's declarations.

## 2. Validate direct mappings

```text
Carrier.destination <-> shipment.country
Carrier.mass -> shipment.weight
Carrier.mass -> shipment.country       # Number to Text: error
```

A bidirectional declaration lowers to two independent directions. The
[declarations](02-direct-mappings/mappings.den) describe authored mappings, without
simulating their runtime value flow:

```den
inbound_mapping(carrier::destination, shipment::country);
outbound_mapping(shipment::country, carrier::destination);
inbound_mapping(carrier::mass, shipment::country);
```

The [library](02-direct-mappings/library/mappings.den) derives bad combinations:

```den
invalid_mapping(F, E) :- mapping_endpoints(F, E), !same_type(F, E);
obligation no_invalid_mappings: empty(invalid_mapping);
```

```text
mappings.den:7:1: counterexample: Obligation no_invalid_mappings: relation is not empty; 1 distinct tuples can be present; showing 1 examples.
  note: Replayed present tuple: shipping::invalid_mapping(carrier::mass, shipment::country).
Result: findings
```

The retained derivation places this at the bad mapping fact. No runtime input is
needed for a static type error, so there is no input-world note. Remove the last
mapping to repair it. A converter, introduced in step 04, is another way to make a
cross-type intent explicit.

**Denotate concepts learned:** Rules derive invalid tuples, `empty` requires their
absence, and retained derivations place findings on the authored facts that caused them.

## 3. Detect conflicting conditional mappings

```text
when Carrier.service is express:
    Carrier.mass -> shipment.weight
when Carrier.service is not standard:
    Carrier.estimated_mass -> shipment.weight
```

These guards overlap: `express` is also not `standard`. The
[consumer](03-guards/mappings.den) records every comparison as metadata and defines
a Boolean helper for each guard:

```den
field_comparison(carrier::service, literals::express);
relation $express_service();
$express_service() :- field_value(carrier::service, literals::express);
applicable_inbound_mapping(carrier::mass, shipment::weight) :- $express_service();
```

The [value library](03-guards/library/values.den) creates a restricted input universe:

```den
field_candidates(F, V) :- field_comparison(F, V), compatible_field_value(F, V);
field_candidates(F, V) :- field_type(F, T), unnamed(T, V);
input field_value(field: Field, value: Value) within field_candidates;
assumption one_field_value: at_most_one(field_value, group_by: field);
```

For the open Text type, `service` can be `express`, `standard`, an unnamed other valid
value, or absent. The selected assumption permits at most one value. A declared but
uncompared literal does not expand that endpoint's input universe. Comparison and
domain-metadata obligations report malformed declarations instead of letting an
accidentally smaller universe silently prove a rule.

No selected value means absent. Equality is then false, and negated equality is
true: **“is not standard” includes absence**. To exclude absence, write an explicit
presence test AND the negated comparison. AND is a conjunction in a rule body;
OR has alternative rules or normalization helpers; NOT uses `!` on its lowered
operand. Parentheses preserve the intended Boolean grouping.

```text
counterexample: Obligation at_most_one_inbound_source is violated: 2 distinct tuples hold in the replayed observation.
  note: Inputs in dependency cone — present: shipping::field_value(carrier::service, literals::express); ...
Result: findings
```

Both applicability rules are primary locations of this one finding. The observation
is restricted to relevant inputs; it is not a dump of every possible field.
Change the fallback to **“is not express”**, and remove its now-unused `standard`
comparison metadata. The guards become complements. Step 04 contains the repair.
Incoming guards read field values; outgoing guards read independent shipment values.
The DSL lowerer must reject operands from the wrong phase; this sample library does
not inspect guard syntax to enforce that rule.
Neither a missing source value nor a mapping declaration implicitly makes a route
inapplicable: applicability is exactly the authored guard.

**Denotate concepts learned:** `input … within` defines eligible input tuples; selected
assumptions constrain their combinations. `at_most_one` detects overlapping mappings
across permitted worlds, and negating a value comparison includes absence.

## 4. Support conversion functions

```text
Carrier.mass -> shipment.weight when Carrier.service is express
Carrier.mass -> shipment.weight when Carrier.service is express and Carrier.mass is present
(Carrier.mass, Carrier.mass_unit) -> unpack_mass -> (shipment.normalized_weight, shipment.display_weight)
(shipment.normalized_weight, shipment.display_weight) -> render_mass -> (Label.mass, Label.unit)
```

The first two lines describe the same directional mapping with alternative guards.
[Step 04](04-converters/mappings.den) introduces `Mapping` identity so repeated
occurrences count once. Direct mapping keys consist of direction and qualified
endpoints. Converter application keys also include the converter and its complete
port bindings in canonical order. Guard text, file positions and binding order are
not identity. The readable constant names here stand in for a lowerer's stable keys;
source provenance belongs to occurrences independently of those keys.

```den
inbound_mapping(routes::measured, carrier::mass, shipment::weight);
applicable_inbound_mapping(routes::measured) :- $express_service();
```

The [converter declarations](04-converters/converters.den) use named typed ports:

```den
converter_argument(unpack_mass::convert, unpack_mass::amount, number);
converter_result(unpack_mass::convert, unpack_mass::display, text);
inbound_converter(conversions::unpack, unpack_mass::convert);
inbound_argument(conversions::unpack, unpack_mass::amount, carrier::mass);
inbound_result(conversions::unpack, unpack_mass::display, shipment::display_weight);
applicable_inbound_mapping(conversions::unpack);
```

The file supplies both arguments and both results. `render_mass` is a separate
reverse-direction function; Denotate does not infer that it is an inverse.
The shared destination projection includes both direct and converter applications:

```den
inbound_destination(M, E) :- applicable_inbound_mapping(M), inbound_mapping(M, _, E);
inbound_destination(M, E) :- applicable_inbound_mapping(M), inbound_converter(M, _), inbound_result(M, _, E);
obligation at_most_one_inbound_source: at_most_one(inbound_destination, group_by: element);
```

```text
Verification shipping::mappings
Result: proved
```

A converter receives nil for absent arguments, so an unconditional application is
applicable even in the all-absent world. Every bound result is a potential write.
Its implementation, returned values and successful execution are not modeled.
Port existence, complete unique bindings, binding types and one output port per
destination within an application remain **lowerer invariants**, not obligations
in this sample. Projecting ports away cannot detect two results of one application
bound to the same destination. “Proved” does not certify those invariants.

**Denotate concepts learned:** Explicit mapping identity distinguishes a mapping from
its occurrences. Relational projection lets the same uniqueness obligation cover
direct mappings and converter destinations.

## 5. Add feature toggles and optional flags

```text
toggle "express-service"
toggle "customs-checks"
shipment.fragile: Flag
render_mass when active "express-service"
shipment.display_weight -> Label.mass when inactive "express-service"
```

[Flags and toggles](05-toggles-and-flags/library/flags.den) have different encodings:

```den
input toggle_active(toggle: Toggle);
closed_type(flag);
value_type(shipping::flags::true, flag);
value_type(shipping::flags::false, flag);
```

The illustrative `active "name"` condition lowers to `toggle_active(...)`;
`inactive "name"` lowers to its negation. A toggle's atom is either present (active)
or absent (inactive). Both toggles can be active together. Flag is a `DataType`
constant with an explicitly closed value domain; the generic candidate rules include
both values even without comparisons.
The endpoint itself can still be absent. This vocabulary declares only true and
false as Flag values; valid literal encoding is a lowerer responsibility. The name
`flag` does not create a built-in or sealed Boolean type in the IR.

| `shipment.fragile` | is true | is false | is not true |
| --- | --- | --- | --- |
| true | true | false | false |
| false | false | true | true |
| absent | false | false | true |

[features.den](05-toggles-and-flags/features.den) switches `Label.mass` between a
converter and a direct mapping on complementary toggle guards. It also chooses a
handling note using `fragile is true` versus `fragile is not true`.

```den
$not_fragile() :- !element_value(shipment::fragile, shipping::flags::true);
applicable_outbound_mapping(ordinary) :- $not_fragile();
```

```text
Verification shipping::mappings
Result: proved
```

Adding Flag did not add `field_flag_value`, `element_flag_value` or a special mapping
relation. Its closed domain is metadata interpreted by the same generic relations.

**Denotate concepts learned:** Input presence models a two-state toggle; a restricted
value relation models true, false or absence. Closed value domains are expressed
through metadata and generic relations.

## 6. Support predicate functions and their contracts

```text
check domestic(Text)
check international(Text)
exclusive [domestic, international]
shipment.handling_note -> Label.routing when domestic(shipment.country)
shipment.routing_note -> Label.routing when international(shipment.country)
```

These function names carry no geographic knowledge. The
[predicate library](06-check-contracts/library/predicates.den) uses one input bit per
endpoint/predicate pair, eligible only for authored, correctly typed uses:

```den
input predicate_result(element: Element, predicate: Predicate) within predicate_candidates;
predicate_holds(E, P) :- element_present(E), predicate_result(E, P);
```

Repeated calls at that endpoint share the bit. Presence is required by the positive
predicate, not by negation: absent is neither domestic nor international, and both
negated tests are true. Nothing executes the function. Checks are assumed pure,
but this model does not enforce equal results for equal values held in different
elements: each element/check pair has an independent bit. It may therefore consider
combinations that a real implementation cannot produce.

An `exclusive` family declaration allows at most one member to hold at the same
endpoint; it permits none. Membership facts derive every distinct pair, avoiding a
second pair inventory:

```den
forbidden_check_results(E, F) :- exclusive_member(F, P), exclusive_member(F, Q),
    !same_predicate(P, Q), predicate_holds(E, P), predicate_holds(E, Q);
assumption predicate_contracts: empty(forbidden_check_results);
```

The library's `shipping::mappings` verification explicitly selects that assumption
alongside the one-value assumptions. It is a trusted promise about the functions,
not a proof of their implementations. Other verifications must select it themselves.
Overlapping families are not transitive: `[A,B]` and `[B,C]` still permit `A` and `C`.

```text
Verification shipping::mappings
Selected assumptions: [shipping::one_field_value, shipping::one_element_value, shipping::predicate_contracts]
Result: proved
```

The three templates in step 06's `exercises/` folder show why context matters.
Copy the step to a fresh scratch folder, then activate one probe at a time;
`.den.txt` templates are inert until copied to a `.den` file:

```sh
scratch=$(mktemp -d)
cp -R editors/den/examples/shipping-news/06-check-contracts "$scratch/program"
cp "$scratch/program/exercises/without-contract.den.txt" "$scratch/program/probe.den"
just check-den "$scratch/program"
```

| Probe template | Expected result |
| --- | --- |
| [without-contract](06-check-contracts/exercises/without-contract.den.txt) | Extra verification reports a routing counterexample; the library verification remains proved |
| [assumed-conclusion](06-check-contracts/exercises/assumed-conclusion.den.txt) | `assumed-conclusion` warning: the selecting verification assumes the relation it claims to audit; its result is proved but circular |
| [inconsistent](06-check-contracts/exercises/inconsistent.den.txt) | Requiring both checks while assuming their exclusivity yields `inconsistent-assumptions`; obligations are not checked |

Replace `probe.den` with the next template, rather than accumulating probes. These
cases currently exit 1. Static signature/type validation uses its own assumption-free
verification, so a trusted runtime contract cannot hide an invalid predicate use.

**Denotate concepts learned:** Selected assumptions express trusted contracts and
define each verification's permitted worlds. Consistency checking and
`assumed-conclusion` warnings expose problems in how a verification is constructed.

## 7. Define reusable classification terms

```text
term dispatch_rules:
    when active "customs-checks":
        shipment.country is present
        domestic(shipment.country) or international(shipment.country)
        when active "express-service":
            shipment.fragile is false
term ready:
    shipment.assessed_weight is present
    dispatch_rules
Label.assessed_mass <- shipment.assessed_weight when ready
Label.assessed_mass <- shipment.weight when not ready
```

`assessed_weight` is supplied by hypothetical middle processing. The
[consumer](07-classifications/classification.den) declares it as another typed element;
its output-phase value is a runtime input to this model, not a computation performed here.

A term conjoins its constraints. A conditional constraint contributes
`NOT (all enclosing guards) OR requirement`. Consequently `dispatch_rules` holds
when customs checks are disabled, even if every element is absent. The separate
presence requirement in `ready` still has to hold.

The lowerer substitutes all ancestor guard expressions into the **whole term**,
then calls the existing Boolean normalizer. `.den` has rules, not inline Boolean
expression syntax; helpers below illustrate normalization output:

```den
$country_requirement() :- !toggle_active(options::'customs-checks');
$country_requirement() :- element_present(shipment::country);
$both_guards() :- toggle_active(options::'customs-checks'), toggle_active(options::'express-service');
$care_requirement() :- !$both_guards();
$care_requirement() :- element_value(shipment::fragile, shipping::flags::false);
dispatch_rules() :- $country_requirement(), $route_requirement(), $care_requirement();
ready() :- element_present(shipment::assessed_weight), dispatch_rules();
```

`Term`, `When` and `ConstraintUse` constants preserve source-use identities.
`term_constraint`, `constraint_when` and `when_parent` retain membership; downstream
`classified` and `when_applicable` relations expose observations. They do not feed
back into term definitions. Formula interning and simplification suggestions are
not implemented. A future lowerer rejects empty terms and cyclic lexical containment;
that does **not** reject recursive term references.

Positive recursion uses the least fixed point. The sample's `attention`/`follow_up`
cycle needs its independent `fragile is true` seed. More subtly:

```text
term self_guard: when not self_guard -> self_guard
```

The whole formula is `NOT NOT T OR T`. Normalization cancels double negation before
creating helpers, leaving positive self-recursion, false at the least fixed point:

```den
self_guard() :- self_guard();
self_guard() :- self_guard();
```

Introducing a named term for `NOT T` first changes the boundary. The
[standalone named-boundary exercise](exercises/named-boundary/program.den) has a
negative cycle. Run `just check-den editors/den/examples/shipping-news/exercises/named-boundary`.
The checker reports `unsupported-region`, with incomplete results and CLI exit 2. Named terms are real
relations, not textual macros; extracting one is not automatically a safe refactoring.
Keeping this exercise small isolates that semantic issue. Composing unsupported
recursion with a larger input universe may instead exhaust certification; exhaustion
is not a proof. The main step remains admitted:

```text
Verification shipping::mappings
Result: proved
```

**Denotate concepts learned:** Whole-formula normalization preserves implication
semantics. Positive recursion uses the least fixed point; named recursive relations
create semantic boundaries that cannot always be introduced by simple extraction.

## 8. Help authors understand their conditions

```text
when active "customs-checks":
    when active "express-service":
        when active "customs-checks": ...     # always true here
        when inactive "customs-checks": ...   # impossible here
            when active "express-service": ...
```

[notices.den](08-condition-notices/notices.den) introduces advisory observations of
these authored uses, separate from the term definitions:

```den
enclosing() :- customs(), express();
notice nested_customs_guard_varies: varies(customs, within: enclosing);
notice nested_not_customs_guard_varies: varies(not_customs, within: enclosing);
notice inner_express_guard_varies: varies(express, within: unreachable);
```

`within` includes both ancestors. Using only the immediate parent's `express`
condition would lose the fact that customs checks are already active. The lowerer
supplies the complete scope; Denotate does not infer lexical nesting.

```text
notices.den:17:12: always-true-condition: Condition is always true in this scope.
notices.den:18:12: impossible-condition: Condition is impossible in this scope.
Result: proved
```

`outer_customs_guard_varies` and `nested_express_guard_varies` vary.
`nested_customs_guard_varies` is always true, `nested_not_customs_guard_varies` is
impossible, and `inner_express_guard_varies` has an unreachable parent. The last
receives no child diagnostic; its `parent-unreachable` state remains visible with
`check-den --json`. Notices do not turn into obligation failures or authorize automatic
rewrites. In a real lowerer,
the notice's provenance points to the authored When, even when formulas are shared.

**Denotate concepts learned:** `varies` notices inspect conditions within an explicit
complete scope. They retain authored-use identities and provide advice independently
of obligation verdicts.

## 9. Review what the completed library guarantees

[09-complete](09-complete/) contains the complete mapping library and consumer. Run its
scorecard separately from diagnostic inspection:

```sh
just score-den editors/den/examples/shipping-news/09-complete --samples 1 --json /tmp/shipping-news-score.json
```

The standard verifications prove the declared static checks and at-most-one mapping
contracts under their selected assumptions; the same two advisory condition notices
remain. No new checker policy or numeric performance threshold is specified here.

| Modeled in steps 1–9 | Deliberately outside steps 1–9 |
| --- | --- |
| Presence and comparison with typed literals | Arithmetic, ordering, unit conversion results |
| Per-endpoint open/closed value alternatives | Equality between different endpoints |
| Conditional potential destinations, including multiple UDF results | UDF execution, success, actual writes or inverse laws |
| Selected exclusivity contracts for predicates | Verification of those promises against function bodies |
| Independent input-phase and output-phase observations | Runtime value propagation, sequencing or correlations between phases |
| Boolean classification and existing recursive admission | Generic formula interning or simplification rewrites |
| Explicit typed-port metadata | Enforcing the port-binding/lowerer invariants listed in step 04 |

The unnamed Text marker means “some other valid value at this endpoint.” Two endpoints
with that marker need not hold the same value. Likewise, a proved overlap obligation
is about distinct mapping identities, not distinct output values or source line counts.

The [phase-gap probe](exercises/phase-gap.den.txt), added to a scratch copy of step 09,
asks whether a present carrier destination guarantees a present shipment country.
It reports a counterexample and exits 1. An actual copy implementation could guarantee
that relationship, but the independent phase inputs do not encode it. The abstraction
can therefore reveal possible conflicts that a more detailed execution model would
exclude; it never claims to have run a message through a converter.

**Denotate concepts learned:** Proofs concern the modeled relationships under selected
assumptions. Counterexamples expose possibilities in that model; the scorecard
measures checking separately from diagnostic inspection.

## 10. Use computed values in task conditions

The [computation lesson](10-computed-values/README.md) follows this chain:

```text
compute_zone → shipment.zone → domestic → prepare_customs → shipment.customs_reference
```

Its small library derives values only when their task applies and the output is
emitted. Possible function results and conditional emission remain inputs. This
replaces the independent workspace observations of step 09 for this focused model;
it does not execute UDFs or implement an execution scheduler.

```sh
just check-den editors/den/examples/shipping-news/10-computed-values
just edit-den editors/den/examples/shipping-news/10-computed-values
```

The lesson includes a validity assumption whose relation-level dependency cycle
disappears at the ground level, sparse output-result contracts, and two runnable
exercises: a task that cannot start itself and a contradictory negative cycle.
Each exercise has a suggested edit and an expected result in the walkthrough.

**Denotate concepts learned:** Open function outcomes can feed derived availability.
Ground dependencies distinguish an ordinary task chain from a real cycle; selected
assumptions must have independent meaning. An unavailable value in a fixed-point
model does not describe a runtime value that has merely not been computed yet.

## Regression checks

The actual `check-den` example's test suite checks the tutorial programs and probe
templates:

```sh
just test-shipping-news
```

Tests enforce every step's outcome and findings, the three repairs and placement,
contract selections, inconsistency, recursive boundaries, the optional-flag truth
table, classification truth across 96 valid worlds, cold/warm agreement, invalid
metadata, and direct/converter collisions. They also check opaque-predicate presence
and endpoint independence, repeated uses, and non-transitive exclusivity across
overlapping families. Tests never pin chosen witnesses or rendered CLI text. The regular crate gate also runs them.
The computation lesson checks all 64 input assignments under each of its two
contexts (8 and 6 permitted worlds), conditional emission, sparse result coverage,
the circular exercises, and cold/warm agreement after an output-contract edit.
