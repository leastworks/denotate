# The `.den` format

`.den` is the text form of the Denotate IR. It is both an authoring format and an
export format: a DSL can print its lowered program as `.den`, with embedded origins
pointing back to the DSL source. The grammar is `grammars/den/grammar.js`; the loader
and printer are in `crates/ir-text`.

## Terms

A DSL on Denotate involves two levels: the DSL program an author writes, and the
data that program receives when it runs. The checker distinguishes facts by when they
are known, not by where they came from.

- **DSL program** (DSL source): what the DSL author writes. It is lowered, not input.
- **Library:** `.den` rules, written once per DSL, that give the DSL its meaning.
- **Lowering:** translates a DSL program into program facts that the library uses.
- **Fixed facts:** `.den` facts that are the same in every world. **Program facts**
  come from lowering a DSL program; **library facts** are written by the library
  author.
- **Runtime input:** an `input` relation, the data the DSL program receives when it
  runs. It is unknown when checking. In this documentation, "input" alone means a
  runtime input.
- **World:** one choice of every runtime input. Fixed facts are the same in all worlds.

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
  worlds. Assumptions support all four cardinality forms over input or independently
  stratified derived relations (see [selected assumptions](#selected-assumptions)).
  Declarations take effect through selection: a [verification](#verifications)
  selects which are checked, and under which assumptions.
- **Names.** Quote any non-identifier or reserved word: `'007'`, `'module'`.
  Escapes: `\\`, `\'`, `\n`, `\r`, `\t`. Parameter names and `group_by` columns accept
  reserved words unquoted. `$condition_N` is a generated helper (zero-arity, derived),
  distinct from a frontend relation spelled `'$condition_N'`.
  Diagnostic tuple notes use canonical `.den` spelling too: uppercase constants
  such as `'F3'` stay quoted, as do hyphenated names such as `flags::'new-mode'`.
  Unnecessary source quotes need not be preserved. This affects display only,
  not semantic keys or finding identity.

## Restricted input domains

An input normally has one possible atom for every combination of its parameters'
resolved sort values. `within` instead names a derived relation whose true tuples
are its entire input universe:

```den
sort S;
const a, b: S;
relation candidate(x: S);
relation excluded(x: S);
relation eligible(x: S);
candidate(a);
candidate(b);
excluded(b);
eligible(X) :- candidate(X), !excluded(X);
input selected(x: S) within eligible;
```

Here only `selected(a)` can be supplied. The provider must have the same arity and
positional sorts as the input (parameter names may differ). Its whole dependency
cone must be input-free and stratified: positive recursion and layered negation are
allowed, but a cycle through negation is rejected, even if some verification's
assumptions could discharge it. Provider references follow ordinary relation lookup,
including namespaces, `use` and forward references. Only inputs can carry `within`;
the clause precedes an optional `loc(...)`.

The checker evaluates this cone exactly before creating input atoms. It uses the
checked program's library closure and resolved sort domains, including `domain`
overrides. Consumers can supply different provider facts to a library input. Domain
evaluation is bounded preparation work; exhaustion yields an inconclusive result
with phase `input domains` and a resource, never a partially restricted universe.

An excluded atom has no Boolean variable. Supplying it as a present observation is
an error. Sort-correct rule references remain valid: positive references are false,
negative references are true. Excluded atoms do not appear in observations, even in
the absent list; derivations may still show an authored negative premise about one.
An empty provider gives zero input atoms. For a zero-arity input, a true provider
tuple gives one atom and a false provider gives none.

Restrictions belong to the input declaration and apply in every verification.
Assumptions constrain assignments within that universe; they do not affect domain
evaluation. Eligibility alone permits the all-absent world; selected assumptions may
exclude it. Coverage groups still range over
the grouping columns' resolved sort domains: an empty provider with sort values
`a` and `b` gives two failing groups for `at_least_one(selected, group_by: x)`.
It does not remove those groups or prove coverage.

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

Coverage failures are aggregated into one finding per obligation and verification.
The finding retains a bounded sample of missing groups, each with its own replayed
input world, and a count of distinct groups that fail in at least one permitted world. Counts
are exact only when checking is complete; otherwise they are lower bounds and the
incompleteness is explicit. Limits bound enumeration as well as checking, preserving
failures already established. Unknown or blocked facts never count as absence.
An independent guaranteed tuple can establish coverage despite other unsupported
producers; a settled failure remains a failure alongside unresolved worlds.

Each retained missing group is placed on the declarations of its constants that
are locatable in the checked program's own files, with the obligation related.
Several grouping columns can therefore give several primary locations for one
group. Locations are unioned across retained examples; shared locations merge their
group and world notes. If a group has no qualifying declaration (`group_by: ()`,
library-only constants or missing current spans), it keeps the obligation placement,
with the labeled library fallback when needed. Upstream origins remain related.
Placement uses only the retained examples; counts, checking and finding identity
are unchanged.

Coverage also constrains worlds when used as a [selected assumption](#selected-assumptions).
Coverage obligations use the same verification selection, unchecked-obligation notices,
names, origins and editor services as uniqueness.

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
Duplicate derivations never create a second tuple. Exactly-one assumptions constrain
both parts together. Names, selection, origins, printing and editor services use the
same shared paths as other obligations.

## Counterexample placement

For a library-declared emptiness or uniqueness obligation, each reported tuple's
retained proof is followed along positive support. The first locatable producer
in the checked program's own files on each branch is primary. Producers include
empty-body facts. Unlocated generated rules do not stop the search; declarations,
argument tokens and negative premises never form the frontier. The rest of the
derivation remains related, including guard helpers below a primary producer.

Frontiers are unioned across tuples: a producer needed for one tuple remains primary
even when it is below another tuple's frontier. A tuple with no locatable consumer
producer keeps its previous placement, including labeled library fallback. The
boundary includes all transitive libraries. Obligations declared in the program's
own files, or with no current declaration location to establish ownership, keep
their previous placement. Only current provenance supplies primaries; upstream
origins remain related.

This changes placement only, not verdicts, finding identities, retained derivations
or attribution status. Coverage uses its separate missing-group constant placement.

## Counterexample world notes

Uniqueness notes restrict the observation to the union of the structural input cones
of the conflicting tuples. Coverage notes use the union of the cones of all candidate
tuples in the missing group, since there is no present violating tuple. Both include
negative dependencies and alternative producers, and omit the input note when the
cone has no inputs. These scopes come from the checker after semantic checking with
an independent bounded allowance per witness. If collection exhausts its allowance,
the note explicitly falls back to the full world. The full replayed observation
always remains in structured evidence. This filtering changes neither verdicts nor
primary/related source placement.

## Emptiness obligations

```den
obligation no_conflicts: empty(conflict);
```

`empty(R)` requires no tuple of `R` in any permitted input world, using the program's
resolved domains and the verification's selected assumptions. It has no grouping;
even `empty(R, group_by: ())` is rejected. A relation with no possible tuples is
proved empty; a zero-arity relation fails as soon as its single tuple is present.
Duplicate derivations do not change this.

One finding per obligation and verification reports up to three distinct,
replay-confirmed present tuples. Each retains its own input world, replay scope and
derivation. The count includes every confirmed tuple, including those beyond the
sample: it is exact when checking completes and a lower bound otherwise. This is a
count across permitted worlds, not a claim that all the tuples occur together.
Repeated derivations or worlds for the same tuple count only once. The sample keeps
the smallest confirmed tuples by semantic key, independently of checking order.

The identity has component `emptiness` and does not depend on the tuples or worlds
shown. Blocked or unknown facts never count as presence. Unresolved worlds and
exhausted limits make checking inconclusive, never proved. Known counterexamples
survive that incompleteness, which remains visible in the message and result.

Failure locations are the union of the retained tuples' derivations: producing
rules (including facts) are primary, narrowed to the ownership frontier for
library-declared obligations as described above. Premise occurrences and the
obligation are related. Normal ownership and labeled library fallback apply separately
to each tuple. Each primary has a note naming its tuple; shared locations merge
those notes. Input notes restrict the replayed observation to the tuple's structural
dependency-cone inputs, collected by the checker from the ground dependency graph.
This includes inputs behind negated derived relations and alternative producers,
even when absent from the selected derivation. A cone with no inputs has no input
note. Cone collection has a separate bounded allowance; if unavailable, presentation
explicitly falls back to the full observation without changing checking or source
attribution. Structured evidence always retains the full replayed world and the
separate cone-input status. Multiple locations still share one finding identity.
Alternative derivations of a tuple are not enumerated.

Attribution runs after checking with a fresh bounded allowance per retained tuple.
If it cannot finish, that tuple falls back to the obligation with an attribution
notice; other tuples keep their own attribution allowances. Verdict and checking
completeness are unchanged. Current `.den` locations and upstream origins remain
separate. Findings without a witness stay at the obligation.

`empty` also constrains worlds as a [selected assumption](#selected-assumptions).
For obligations, selection, unchecked-obligation notices,
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
  `[]`. `assumptions: []` permits every assignment over the declared input universe.
  An optional `notices: [...]` list follows `obligations`. With no obligations or
  notices selected, the verification is consistency-only: semantic analysis still
  runs and the declaration gets a warning. Selecting only notices is allowed and
  gets no consistency-only warning.
- References follow the usual namespace lookup and resolve only to their own kind; an
  unknown, wrong-kind, ambiguous or repeated reference is an error. `verification` is a
  reserved word; `assumptions`, `obligations` and `notices` are not.
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

## Contextual condition notices

A runnable [editor example](../editors/den/examples/condition-notices/README.md)
shows each conclusive case.

A notice asks whether a Boolean condition varies within a specified scope, under
one verification's selected assumptions. It is advisory: it does not assert an
obligation or change the verification's verdict.

```den
input selected();
input eligible();
relation parent_scope();
parent_scope() :- selected(), eligible();
notice repeated_selection: varies(selected, within: parent_scope)
    message "Nested condition";
verification authoring {
    assumptions: [];
    obligations: [];
    notices: [repeated_selection];
}
```

This reports Information: the condition is always true whenever `parent_scope`
holds. `varies` takes a zero-arity input or derived relation; optional `within`
takes another zero-arity relation and defaults to true. References use ordinary
relation lookup. `notice` and `within` are reserved; `varies` and `notices` are contextual
words. The declaration supports `loc(...)` origins. An optional message prefixes the
explanation; it is a label, not a replacement for the checked result.

Let W be the permitted-world condition, P the complete enclosing scope, and G the
condition being inspected. W must be consistent before any notice can be concluded.

| Result | Meaning |
| --- | --- |
| `impossible` | P has a replayed permitted witness, but P AND G has none; Warning. |
| `always-true` | P has a replayed permitted witness, but P AND NOT G has none; Information. |
| `varying` | Both sides have replayed permitted witnesses; no diagnostic. |
| `parent-unreachable` | No permitted world satisfies P; no child diagnostic. |
| `unknown` | Required meaning or checking work is unsupported or incomplete; Information (`unanalysed-condition`). Inconsistent assumptions produce only the context Error. |

`within` must describe **all** enclosing conditions, not just the immediate parent's
own condition. The author/lowerer supplies this relation; the checker does not infer
lexical nesting or assume a containing conclusion or sibling requirements. Give an
ancestor its own notice to report its impossibility; children with unreachable
parents then remain quiet. Recursive relations keep their existing meaning.

Each notice has its own semantic identity, even when two notices inspect the same
relation. Findings identify both notice and verification. The notice's declaration
is primary, its condition and enclosing-scope declarations are related, and upstream
origins remain available. Normal program ownership and labeled library fallback
apply. A lowerer can attach the authored condition's origin to the notice.

An unknown notice produces one Information diagnostic at that declaration. Unsupported
dependencies include the blocking cycle's rules as related locations; exhausted limits
name the phase and resource, and deadlines name the phase and deadline. The checker
retains this cause. An inconsistent context gets only its existing Error, and a query
not reached because prerequisite checking failed produces no extra condition diagnostic.
These advisory findings do not change verdicts, completeness, aggregate status or CLI
exit codes. A notice that later becomes decidable keeps the same finding identity.

Selected notices appear in the status summary, including quiet and unknown results.
Each is a separately bounded checker query after obligation checking; exhausting a
notice's allowance cannot spend an obligation's allowance or turn an unknown into a
proof. Its evidence retains complete replayed worlds; ordinary messages omit world
lists. Notices make no automatic rewrite suggestions. Unselected notices are inert
and do not generate unchecked-obligation warnings.

## Selected assumptions

Assumptions have the same cardinality vocabulary as obligations: `at_most_one`,
`at_least_one`, `exactly_one`, and `empty`. Grouping uses the program's resolved
sort domains, including overrides. `group_by: ()` has one global group; an empty
grouping domain has no groups. `empty` takes no grouping argument.

```den
input selected();
relation missing();
missing() :- !selected();
assumption required: empty(missing);
verification check_presence { assumptions: [required]; obligations: []; }
```

The full dependency cone of an assumption relation must be stratified independently
of assumptions: positive recursion and stratified negation are allowed, cycles
through negation are declaration errors even if a selected context could discharge
them. These rules may depend on inputs. This differs from `within` providers, which
must be input-free. Construction clients call `Corpus::validate_assumptions` after
building rules; text loading and request preparation perform the same validation.

Before admission, the checker evaluates these cones without assumptions or rewrites
and conjoins their cardinality conditions into the permitted-world condition W.
W must allow at least one world. Otherwise that verification reports
`inconsistent-assumptions` and checks no obligations; a consistency-only verification
uses the same test. Exhaustion is inconclusive and cancellation aborts the run.
Admission, rewrites, no-meaning analysis, obligation checks, replay and certification
all use this W. Input eligibility and grouping domains do not change with selection.

An `assumed-conclusion` warning appears on the selecting verification when an
assumption constrains an obligation's relation or a relation transitively derived
from it. The assumption and obligation declarations are related locations. The
reverse direction is ordinary assume-guarantee reasoning and does not warn; sharing
inputs, fixed facts or another derived intermediate does not by itself warn.
Warnings do not alter the selected context or its results.

## Meaning

A program's meaning is defined separately for each **permitted input world**: a choice
of eligible input tuples over the finite domains that satisfies the assumptions
selected by the verification being checked. In each world, the derived relations hold
exactly the least fixed point of the rules. Admission, rewrites, no-meaning and
unsupported findings below are therefore per verification: the same program can be
admitted under one verification and unsupported under another, while the meaning of
a fixed world never depends on the verification.

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
just check-den <folder-or-den.root> [--verification QUALIFIED_NAME] [--json] [--verbose]
just export-test-dsl <out-dir> <file.testdsl>…   # export a DSL program as .den
```

`check-den` runs each verification declared in the program and its reachable libraries,
printing its name, selected assumptions and presented diagnostics. Each diagnostic
shows its source URI, one-based line and Unicode-scalar column, kind, message, notes
and labeled related locations. By default, related locations show producing rules,
the checked obligation and upstream origins. Other related entries collapse to
"+N more related locations"; `--verbose` prints the full list. Primary locations,
messages and notes are unchanged by this option. This is a CLI layout choice;
the editor keeps all related information.

Verifications follow semantic-key order; diagnostics and related locations follow
source URI and numeric coordinate order, with content
as a tie-breaker. Notes are sorted by text. Library fallback messages retain their
`in <program>:` label. Each verification ends with its status.

`--json` retains the previous per-verification `Results: {...}` status summary
instead of human diagnostics. Root/verification headers and configuration notices
remain, so this mode is not a single JSON document. Exit codes are the same in both
modes. `--verbose` has no effect with `--json`. With no verification it prints
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
