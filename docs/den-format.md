# The `.den` format

`.den` is the text form of the Denotate IR. It is both an authoring format and an
export format: a DSL can print its lowered program as `.den`, with embedded origins
pointing back to the DSL source. The grammar is `grammars/den/grammar.js`; the loader
and printer are in `crates/ir-text`.

## A small program

```den
namespace demo;
sort S;
const a, b: S;
input value(x: S);
relation present(x: S);
present(X) :- value(X);
assumption unique_input: at_most_one(value, group_by: ());
obligation unique_output: at_most_one(present, group_by: ())
    message "At most one value.";
domain S = [a, b];
verification single_value {
    assumptions: [unique_input];
    obligations: [unique_output];
}
```

- **Sorts and constants.** A sort's domain defaults to all its declared constants in
  the program (none means empty). One `domain Sort = [...]` may override it.
  Constants used by rules must belong to the domain.
- **Relations** are `input` (supplied by the environment) or derived (`relation`).
  Inputs cannot be defined by rules.
- **Rules** are `head :- body` with positive and `!`negated atoms; facts have no body.
  Variables are uppercase identifiers or `?'any name'`; `_` in a positive body is a
  fresh variable. Integers are typed constants (`01` canonicalizes to `1`).
- **Contracts.** `obligation name: at_most_one(rel, group_by: (cols))` is a property to
  check; `obligation name: at_least_one(rel, group_by: (cols))` checks coverage.
  `obligation name: exactly_one(rel, group_by: (cols))` requires both coverage and
  uniqueness; `obligation name: empty(rel)` requires no tuples.
  `assumption name: at_most_one(input, group_by: (cols))` restricts input
  worlds. Only input `at_most_one` assumptions are supported. Declarations take
  effect through selection: a [verification](#verifications) selects which are checked, and under which
  assumptions.
- **Names.** Quote any non-identifier or reserved word: `'007'`, `'module'`.
  Escapes: `\\`, `\'`, `\n`, `\r`, `\t`. Parameter names and `group_by` columns accept
  reserved words unquoted. `$condition_N` is a generated helper (zero-arity, derived),
  distinct from a frontend relation spelled `'$condition_N'`.

## Coverage obligations

`at_least_one` requires a tuple for every grouping tuple in every permitted input
world. Groups come from the program's resolved domains, including `domain S = [...]`
overrides. They include combinations with no possible producing tuples: checking
only existing facts would miss the omissions that coverage is meant to detect.

```den
obligation complete_assignment: at_least_one(assignment, group_by: (customer));
```

This requires an assignment for every customer in the resolved customer domain.
`group_by: ()` instead creates one global group and requires a nonempty relation.
If a grouping column's domain is empty, there are no groups: coverage is proved,
with an Information note on the obligation, “no groups: the grouping domain is
empty”. The global group is always present, even if the relation has no possible
result tuples, and never receives that note. Duplicate derivations count as one tuple.

Coverage failures are aggregated per obligation and verification. The diagnostic
shows a bounded sample of missing groups, each with its own replayed input world,
and a count of distinct groups that fail in at least one permitted world. Counts
are exact only when checking is complete; otherwise they are lower bounds and the
incompleteness is explicit. Limits bound enumeration as well as checking, preserving
failures already established. Unknown or blocked facts never count as absence.
An independent guaranteed tuple can establish coverage despite other unsupported
producers; a settled failure remains a failure alongside unresolved worlds.

Coverage is an obligation form only. Richer assumption forms remain future work. Coverage declarations use the same verification
selection, unchecked-obligation notices, names, origins and editor services as uniqueness.

## Exactly-one obligations

```den
obligation one_assignment: exactly_one(assignment, group_by: (customer));
```

This is one declaration with two independent checks: every customer in the program's
resolved domain has at least one assignment, and no customer has more than one distinct
assignment. Both checks use the verification's selected assumptions; neither check is
assumed while proving the other. `group_by: ()` requires exactly one tuple overall.

Both parts must prove for the obligation to be proved. Both failures are reported,
even when they occur in different input worlds. Coverage failures are aggregated as
above; uniqueness retains one finding per overlapping group. A known failure remains
a failure if the other part is unsupported or inconclusive, and that incompleteness
remains visible. Findings label their coverage or uniqueness component.

With an empty grouping-column domain, both parts are vacuously satisfied and the
coverage Information note remains. With a zero-arity relation or grouping by every
column, uniqueness is trivial because tuples are distinct; coverage still has to prove.
Duplicate derivations never create a second tuple. Exactly-one assumptions are not
supported. Names, selection, origins, printing and editor services use the same shared
paths as other obligations.

## Emptiness obligations

```den
obligation no_conflicts: empty(conflict);
```

`empty(R)` requires no tuple of `R` in any permitted input world, using the program's
resolved domains and the verification's selected assumptions. It has no grouping;
even `empty(R, group_by: ())` is rejected. A relation with no possible tuples is
proved empty; a zero-arity relation fails as soon as its single tuple is present.
Duplicate derivations do not change this.

One finding per obligation and verification reports a replay-confirmed present tuple
and its input world. The identity has component `emptiness` and does not depend on
which tuple or world is shown. Blocked or unknown facts never count as presence.
Unresolved worlds and exhausted limits make checking inconclusive, never proved.
A known counterexample survives that incompleteness, which remains visible in the
message and result. The diagnostic is placed at the obligation, using the normal
labeled fallback for library declarations.

`empty` is an obligation form only. Selection, unchecked-obligation notices,
consistency-only verifications, origins, printing and editor services work as for
other obligations.

## Verifications

```den
verification normal_operation {
    assumptions: [one_value_per_input, lib::one_request_per_customer];
    obligations: [unique_assignment];
}
```

- A verification names the assumptions that define its permitted input worlds and the
  obligations checked in them. Both lists are required, in this order; either may be
  `[]`. `assumptions: []` means unrestricted inputs. `obligations: []` is a
  consistency-only verification: semantic analysis still runs, but no obligation is
  checked, and the declaration gets a warning.
- References follow the usual namespace lookup and resolve only to their own kind; an
  unknown, wrong-kind, ambiguous or repeated reference is an error. `verification` is a
  reserved word; `assumptions` and `obligations` are not.
- Declaring or importing an assumption activates nothing. The same obligation can be
  checked under several verifications, each with its own results.
- Every verification in a program's closure runs in that program: a library's
  verifications run in the library's own program and in every consumer, with that
  consumer's facts and domains. A consumer may add verifications over library
  declarations; it cannot replace or weaken an included one. Domains are per program,
  not per verification.
- A program with no verification gets **no semantic checking**: syntax, resolution and
  type errors are still reported, but no implicit context is ever assumed. An
  obligation that no verification in the program selects gets a notice, also when it
  is declared in a library.

## Meaning

A program's meaning is defined separately for each **permitted input world**: a choice
of input tuples over the finite domains that satisfies the assumptions selected by the
verification being checked. In each world, the derived relations hold exactly the
least fixed point of the rules. Admission, rewrites, no-meaning and unsupported
findings below are therefore per verification: the same program can be admitted under
one verification and unsupported under another, while the meaning of a fixed world
never depends on the verification.

- Positive recursion is admitted.
- A cycle through negation is admitted only with a justification: a proof that the
  negation is redundant under the other premises and the assumptions (for example two
  rules with mutually exclusive guards that each negate the other's head), or a
  certification of one world's meaning. Redundant negations are reported as warnings;
  they never authorize edits.
- Otherwise the affected component and everything depending on it is reported as
  **unsupported**, never treated as false, or as **no meaning** where some permitted
  input has no consistent result.
- Obligations are checked over every permitted world. A **counterexample** is reported
  only after concrete replay confirms it; exhausted limits give an explicit
  **inconclusive** outcome.

## Namespaces

- `namespace a::b;` applies to the rest of the file; `namespace a::b { ... }` blocks
  allow several namespaces per file and nest. Namespaces can span files. Top-level
  declarations without a namespace are global. `module a;` is a deprecated alias of
  the file-scoped form. Only `use` lines and comments may precede a file-scoped header.
- Segments are decoded names: `'a::b'` is one segment, `a::b` two.
- `use a::b;` opens names for its file or block. It loads nothing, is not transitive
  and does not open nested namespaces. Code also sees enclosing namespaces.
- Qualified references always start from the global namespace; `::name` selects a
  global declaration. An unqualified name visible from several namespaces is an
  error (inner names do not shadow outer ones).
- All declarations are installed before rules, so files in one namespace can refer to
  each other without `use`. Duplicates are rejected across the whole namespace.

## Programs: `den.root`

A program is defined by a `den.root` JSON manifest:

```json
{"libraries": ["../common/den.root"]}
```

`libraries` lists other manifests by paths relative to this one, each ending in
`den.root`; `{}` means no libraries. A root contains every `.den` file under its folder, stopping
at nested roots. Library roots are included transitively; diamonds and cycles are
visited once. The root's own files are user-owned; reachable library files are
library-owned. There is no implicit root: a `.den` file outside every `den.root` is a
standalone one-file program. Membership never depends on `use`.

## Embedded origins

Origins use MLIR-style locations. Source entries and aliases are file-local and may
be forward-referenced:

```den
p() loc(#positions);
#src = source("file:///example.dsl", view: "dsl", hash: "sha256:ba7816bf…");
#positions = loc(#src { self: 1:1 to 1:4, head: 1:2 to 1:3 });
```

- Coordinates are one-based lines and **Unicode scalar** columns; ranges are
  half-open. Only LF advances a line; CR, BOM and non-BMP characters each count as one
  scalar. A source is identified by URI, view and the SHA-256 of its exact bytes
  (no newline or Unicode normalization).
- Scalar form `loc(#src 1:1 to 1:4)`; several origins `loc(fused[#a 1:1 to 1:2, #b 2:1 to 2:3])`.
  Occurrence maps assign origins per position: `self`, `head`, `head.N`, `body.N`,
  `body.N.M` (zero-based), and `decl.N` for grouped constants. Compact maps
  (`loc(#src { … })`) are equivalent when one source covers every position.
- Undefined, cyclic, duplicate or wrong-kind aliases, malformed hashes and nonexistent
  positions are load errors, including in unused aliases. If a source is missing or
  changed, the loader reports a notice per source and checking continues over the
  current `.den` text.

Every loaded program also has **current `.den` provenance**: every declaration, rule,
atom and term maps to its exact span in the current text, whether or not origins
are embedded. Upstream origins are kept in a separate table.

## Identity

Semantic keys use namespace-qualified declaration identities, never files or source
positions. Rule keys use the rule's namespace, its resolved structure and a duplicate
ordinal. Comments, whitespace, location syntax, moving a declaration between files in
one namespace, and switching between qualified and unqualified spellings of the same
reference do not change keys. Rule order is preserved within a file; cross-file
interleaving is not part of a program's meaning.

## Printing

`ir-text::print` writes an API-built program as `.den` given an explicit file layout.
Names print bare when legal for their kind (constant `i`, variable `I`, integer `1`)
and are qualified only where lookup from the owning namespace would be ambiguous.
Library files go under `library/` with their own root. Output without embedded
origins still reloads with full current-text provenance.

## Commands

```sh
just check-den <folder-or-den.root> [--verification QUALIFIED_NAME]
just export-test-dsl <out-dir> <file.testdsl>…   # export a DSL program as .den
```

`check-den` runs each verification declared in the program and its reachable libraries,
printing its name, selected assumptions and results. With no verification it prints
`No verification configured` and runs no semantic checks. `--verification` selects one
declaration using the usual quoted/qualified name syntax; a bare name must be unique
across the closure. Unknown or ambiguous names are errors. Every filtered run is labeled
partial, even if the program contains only one verification.

Obligations that no verification in the closure selects are listed as unchecked, also
in a filtered run. A verification with `obligations: []` is reported as consistency-only.

Exit codes: **0** for a complete run with conclusive checks, no findings and no unchecked
obligations (a consistency-only notice alone does not fail the run); **1** for findings;
**2** for incomplete, invalid, unconfigured or partial runs, including unchecked
obligations; **3** for filesystem or other operational failures. Incomplete or partial
status takes precedence over findings. The `.den` editor applies the same policy,
checking every verification in the background.
