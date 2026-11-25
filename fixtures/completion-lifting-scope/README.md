# Presence simplification and existence cubes

This repro separates removal of a redundant premise from the scope of the
classification equations. All three programs have one endpoint, three candidate
values, and received and written producers for each value. Presence has one
single-atom producer per value.

- `redundant`: `matched() :- present(item), value(item, v0)`.
- `removed`: `matched() :- value(item, v0)`.
- `retained-scope`: the second form, plus an always-false reader of presence
  from `accepted`. This keeps the original live-GFP classification scope while
  allowing the same search-free simplification.

Each has an unrestricted verification, a scalar-assumption contrast, and a
verification accepting an absent selected value. The unrestricted case permits a
set of values; the scalar case is not a valid optimization for that endpoint.

```sh
just check-den fixtures/completion-lifting-scope/redundant --engine sat --completion-prune --verbose
just check-den fixtures/completion-lifting-scope/removed --engine sat --completion-prune --verbose
just check-den fixtures/completion-lifting-scope/retained-scope --engine sat --completion-prune --verbose
```

The CLI can prove these acyclic programs' existence without lifting cubes. The
checker harness isolates that operation by directly exercising H-coverage encoding,
model replay, cube construction and lifting. It uses an authored observation:
`readable(item)` is true, `received(item, v0)` is either true or false, and every
other input is false. When v0 is absent, H is `!matched()`.

```sh
just test-crate denotate-check --lib lifting_scope_tests -- --nocapture
```

The harness also generates 297 values. Under the old full-view cube algorithm,
both present and absent observations retain all the other values' equations even
after the presence premise has been removed. The current existence projection
keeps the cyclic components and H with their providers, then reconstructs the
acyclic remainder before validating the original equations.

Measured model encodings, excluding the separate input-universe/W encoding:

| Values | Old redundant form: variables / clauses | Current redundant form | Source rewrite |
| --- | --- | --- | --- |
| 3 | 10 / 27 | 5 / 11 | 5 / 11 |
| 297 | 598 / 2,085 | 5 / 11 | 5 / 11 |

With no scalar assumption, the old cube retains 6 pins for three values, or 594
for 297. The current cube starts and finishes with two pins, matching the source
rewrite and the retained-scope control. Present and absent cases agree, as do
pruning off/on and reused H views. A scalar assumption can also lift the extra
pins in the old present-value case; it cannot be imposed on a set-valued endpoint.
These are measurements, not numeric goldens or guarantees about private programs.

The omitted equations are not forgotten. Changing an extra received or written
input may change a value or presence atom, but those acyclic equations always have
an extension. A cyclic omitted equation would not have that guarantee, so every
cyclic SCC, including positive self-support, stays in the existential query.
Frozen classification membership, ambiguity and property checks are unchanged.

Tests also compare every small input world with the direct acyclic equations,
exercise an actual cyclic classification-existence search against enumeration,
and reconstruct every model of tiny signed programs from the retained core. The
broader regression covers formula pins: contradicted producers become inactive
without requiring covered-producer proofs, while their source slots remain for
replay.
