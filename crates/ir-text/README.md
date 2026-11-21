# denotate-ir-text

The `.den` format library: parsing, strict loading into a checked program, printing,
embedded origins, folder-root membership and the incremental editor index. The format
itself is described in [docs/den-format.md](../../docs/den-format.md).

It compiles the committed parser generated from `grammars/den` (needs a C compiler, not
Node). Apart from the `filesystem` command adapter it accesses no filesystem: callers supply
program membership and authoritative snapshots.

## Loading

`load(&ProgramMembership, &[SourceFile])` returns a `LoadedProgram`: `Corpus`, semantic
keys, finite domains, exact current `.den` provenance, documents
with their ownership, and occurrence owners. It requires snapshots for every reachable
member, ignores unrelated documents and rejects conflicting snapshots of one URI.

Named assumptions and verifications are declarations in `Corpus`, with typed semantic
keys and occurrence-based provenance (including embedded origins). There is no separate
loader-owned assumption table. `verification_requests(limits)` returns one
`(VerificationKey, CheckRequest)` per verification in the whole reachable closure,
sorted by key; it returns an empty list when no verification is declared. Each request
selects exactly its declaration's assumptions and obligations. References use shared
namespace lookup and resolve only the kind required by their list.

Verification options also carry `semantics` (stable by default) and an optional
zero-arity `hypothesis` relation and an optional `decisions: [...]` relation set.
Omitting decisions keeps all-relation determinacy; an empty list checks no uniqueness. `no_rejections(H)` is an obligation-only query;
loading validates its selection against a completion verification with the same H.
Printing preserves these options, references and origins; the shared editor index
supports navigation, relation completion and validated rename of verification
hypotheses, decision lists and `no_rejections` relation references. The SAT CLI checks completion with full meaning
analysis; BDD, editor, scorecard and planning consumers still refuse it before stable
preparation. Stable with a hypothesis or selected decisions remains unsupported.

`load_with_resolver(…, Some(&mut resolver))` also restores embedded origins through a
caller-owned `origins::OriginResolver` (one resolution per URI/view/hash identity).
`&Sources` resolves in-memory snapshots; `filesystem::FileOriginResolver` reads local
files for commands. Upstream origins land in `embedded.provenance`, separate from
current provenance; unavailable or changed sources produce `embedded.notices` and no
fabricated spans.

Restoration builds a current-document/range index once per load when annotations
are present. It batches each upstream source's requested coordinates into one
forward scan, including within long lines; it stores only requested boundaries.
These indexes belong to the supplied snapshots and are not caches across edits.

To measure loading with an abstract generated program:

```sh
just bench-den-origins 80 100
just bench-den-origins 10 100 1000000 --long-line
```

Arguments are file count, items per file (default 100), upstream source padding
(default 0), and optional `--long-line`. Each item generates an annotated constant,
fact and rule. The release benchmark compares omitted, unavailable and resolved
origins, reports discovery/loading/checking separately, and checks the same proved
outcome at default limits. Generated files are temporary. Timings are measurements,
not test expectations; this is a loader benchmark, not a production scorecard.

`ProgramMembership` holds the selected root and `RootInfo { files, libraries }` per
root; `ProgramMembership::single` builds an in-memory one-root program.
`filesystem::discover` resolves `den.root` folders on disk for the CLI.

Input declarations may name a provider with `within relation`. Loading resolves it
through the shared relation resolver and delegates signature and dependency-cone
validation to `Corpus`. The provider reference participates in navigation, rename
and completion; export prints it from `Relation::input_domain`.

## Printing

`print(&ExportProgram, PrintOptions) -> Result<ExportBundle, ExportError>` is pure. It
takes the corpus, domains, sources, provenance and an explicit `ExportLayout`
(a file for every top-level occurrence, including assumptions and verifications), and returns
named files plus root manifests. Library files go under `library/` with their own
root. `ExportBundle::documents(base_uri)` reloads a bundle in memory.
`PrintOptions { embedded_origins: false }` omits origins.

Assumptions and verifications are printed from IR declarations with ordinary
top-level layout placements and provenance. There is no separate export assumption
record; API callers declare both contracts in the corpus before exporting.

`spelling(name, NameKind)` is the kind-aware spelling used by the printer; editors must
use it for replacement names (rename). `presentation::diagnostic_names(corpus)`
provides the same kind-aware spelling and qualified names to the shared presenter.
Generated helper labels share the exporter's allocator, including replacements for
invalid or duplicate API labels. Both frontends use this callback for shared tuple
notes; the test DSL retains its own decoded observation vocabulary.

`at_least_one`, `exactly_one` and `empty` obligations load and print through ordinary
contract declarations and named assumptions. Loading classifies assumption cones
through shared IR validation; selected cones needing grounding are validated by the
checker after fixed-truth specialization, independently of selected constraints.
Unselected ground cones stay deferred; loading alone does not establish their validity.
`empty(R)` has no grouping argument, and supplying one is a syntax error. Exactly-one
remains one declaration and selection through printing and reloading. Grouping uses
resolved domains, including explicit overrides. Coverage results and diagnostics are described in the
[format](../../docs/den-format.md#coverage-obligations).

## Committed-program experiments

`committed::write_committed` streams one verification's committed ground graph to
a caller-owned writer under independent work, byte, deadline and cancellation limits.
It includes resolved domains, exact input eligibility, fixed true facts and the
whole residual program. Shared replacement expressions become shared helper
relations. Selected assumptions refer to separate, original ground dependency cones;
otherwise a rewrite justified by an assumption could weaken that very assumption
on reload. This preserves the permitted worlds as well as meaning within them.

The CLI exposes this as `--export-committed FILE`. Choose a new `.den` file in a
separate folder containing a `den.root` with `{}`; then run that folder normally:

```sh
just check-den <source-program> --verification checks --export-committed <resume-folder>/committed.den --stop-after-round 3
just check-den <resume-folder>
```

With several verifications, `--verification` is required. Export runs on admission
completion or interruption, including its deadline. `--stop-after-round N` stops
after the entire round (possibly several commits), skips checking, and returns 2.
If admission finishes before N, checking continues normally. The stop works with
`--no-progress`, uses no cancellation token, and never caches partial admission as
complete. Ctrl+C retains its existing behavior; it does not promise an export.

Output streams through a sibling temporary file and is published atomically without
overwriting an existing file. A failed export reports its cause and publishes
nothing; exporting alone does not change the check's verdict or exit status.
`--export-max-work`, `--export-max-bytes` and `--export-timeout-ms` default to
100 million work units, 1 GiB and 120 seconds, independently of admission limits.

The header records the source digest, build base commit (local changes may be
present), selected declarations, round and state. This is a local experimental artifact, with names intact. It contains no
original `loc(...)` origins: locations and identities refer to the new ground source;
warnings for already-applied executable rewrites disappear; copied assumption cones
can still receive warnings of their own. Warning removal can change a resumed CLI
exit from findings to proved without changing any obligation conclusion. It retains
no BDDs or proofs, and resuming still repeats loading, grounding, preparation and symbolic evaluation.
Compare obligation/notice conclusions, not diagnostic identities or warning counts.

## Editor index

`index::Index` is the recoverable editor boundary. The editor supplies each file's
`SourceFile` and incremental Tree-sitter tree plus explicit membership. The index
shares name decoding, visibility and lookup keys with the strict loader, keeps
per-file projections with current anchors, and resolves per program on demand with
Salsa-tracked queries. Trivia refreshes anchors without invalidating answers; damaged
signatures suppress cascades. It does not need a successfully loaded `Corpus`.

Verification declarations retain their contract kind and projected reference lists.
The index and loader share list resolution, including wrong-kind, ambiguous and
duplicate-reference errors. Typed contract references also drive navigation and validated
rename. Completion uses the same candidates, restricted to assumptions or obligations
by the list being edited, including empty and unfinished lists.

Rule linting comes from `denotate-analysis`.

## Presentation

`presentation::present(&LoadedProgram, &CheckedReport)` adapts the shared presenter
for `.den`: current provenance supplies primaries, upstream origins are related, and
user files are the program's own documents.

## Commands and tests

```sh
just check-den crates/ir-text/fixtures [--verification library::default_checks] [--json] [--verbose]
just check-den <program> --empty-examples all
just check-den <program> --timeout-ms 60000 --max-work 100000000
just check-den <program> --json --no-progress
just check-den <program> --profile-memory /tmp/den-memory.jsonl
just check-den --help
just plan-den fixtures/execution-plan --verification checks --output result
just test-crate denotate-ir-text
```

`just plan-den` is an experimental export command for plain Boolean execution
plans. It requires explicit verification/output selections and unique meaning in
the original upstream union of the output atoms, then emits a semantic-keyed
dependency plan with source origins. Version 3 reports `meaningScope`, including
cone sizes and `outsideAnalysed: false`, on ready and unsuccessful builds (sizes
are null if preparation did not finish). It includes nested scheduling branches
and their joined result bindings; constant
names are `{namespace, name}` objects. `fixtures/execution-plan-branches` demonstrates
a split with default limits. Construction bounds include `--max-split-depth`,
`--max-splits`, `--max-split-candidates` and `--max-support-trials`.
The output is conditional on validated permitted inputs; this command does not run it. See the
[plan API, interpreter and limitations](../plan/README.md).

`examples/check.rs` backs `just check-den`, which builds it optimized (`--release`).
By default it prints shared presented diagnostics grouped by verification: source URI,
one-based line/Unicode-scalar column, kind, message, notes and labeled related
locations. By default only producing rules, the checked obligation and upstream
origins are expanded; other related entries collapse to "+N more". Direct structural
rewrite justifications remain visible. `--verbose` prints all related locations and
requests full structural rewrite chains and notes; the default computes only bounded
direct evidence. `--json` retains the previous `Results: {...}` status summaries with
their existing headers and notices. Ground validation covers the assumptions selected
by the executed verifications (`--verification` narrows this union). Deferred
unselected assumptions receive Information diagnostics without making the run
incomplete. For an authoring check of every declaration, including without
verifications, use `--validate-all-assumptions`; this validates their cones without
activating their constraints.

Experimental SAT checking is opt-in:

```sh
just check-den <program> --engine sat
just check-den <program> --engine sat --verification library::checks --json
just check-den <program> --engine sat --sat-max-worlds 4096 --sat-max-solves 512
just check-den <program> --engine sat --sat-meaning none
```

BDD remains the default. For stable verifications, SAT checks original stable semantics without BDD W or
admission: symbolic `empty` and `at_most_one`, plus **all fixed obligations** whose
relations were settled by input-independent preparation. Symbolic `at_least_one`,
`exactly_one` and notices are explicitly **not analysed**. Notices stay advisory.
Human output uses shared property diagnostics and separately labels context,
whole-program existence and uniqueness. JSON identifies `backend: sat`, separates
`context`, `meaning`, `obligations`, `notices` and `findings`, and retains no-meaning
worlds and differing truth assignments for multiple meanings. A property with no
violating stable model never hides a no-meaning or multiple-meaning world.

`--sat-meaning full|uniqueness|none` selects both meaning checks (default), only
uniqueness, or neither. Skipped phases say `not-analysed`, with reason
`disabled-by-option`; both partial modes keep exit **2**, even with confirmed
property failures. Properties remain visible, and fixed structural results retain
their wording and scope. Skipping meaning does not change the property's stable
semantics: `p() :- p();` still cannot supply a present `p` in a stable model.
It removes totality checking, not the distinction from a completion-only compiler.

`--sat-meaning cone` selects obligation-scoped checking. It requires a nonempty
permitted context, existence in every permitted world, and all selected obligations
proved. Uniqueness is deliberately not analysed and does not prevent exit **0**.
A counterexample or no-meaning world retains exit **1**; exhaustion or an unsupported
obligation kind retains exit **2**. Partial verification selection still keeps exit 2.
The human output names "obligation cones", gives their size, and says "outside not
analysed". JSON `meaning.scope` is `obligation-cones`, `coneSize` contains `atoms`
and `ruleInstances`, and `outsideAnalysed` is false. The sizes include the original
grounded dependency cone's fixed evidence, before SAT simplification.

Both meaning and property queries use isolated cone equations. Downstream rules
cannot eliminate a violating cone model. Selected assumptions outside the cone
still restrict W, through their separate encoding. `full` retains whole-program
semantics; `cone` does not claim that the rest of the program has meaning. There is
no CLI cone-uniqueness switch in this increment.

SAT preparation automatically discovers input facts forced by W and folds the
verification-local view. `Input pins` / JSON `inputPins` reports attempted, proved,
unknown and truncated discovery. Meaning can then split once over a declared
exactly-one input group, ranking by structural propagation. `Meaning split` / JSON
`meaning.split` reports the group, completed candidate count, ranking cutoff, and each
arm's existence/uniqueness state and whether it was stratified. Split-based results
do not fabricate aggregate unsplit existence/uniqueness counters.

`--sat-split RELATION` optionally restricts candidates to a qualified input relation.
The default caps are 256 pin candidates, 8 split candidates and 32 members per
group. Pin-query and ranking work each inherit checker `--max-work`; optional
smaller caps can be supplied. The flags are
`--sat-max-pin-candidates`, `--sat-max-pin-work`, `--sat-max-split-candidates`,
`--sat-max-split-members`, and `--sat-max-split-work`. Zero candidate limits disable
the respective search. Ranking does no SAT; actual arms use isolated W-pinned
solvers, ordinary per-branch phase allowances, and a shared remaining deadline.
No nested or derived-family split is attempted. An unknown branch cannot be skipped;
known failures remain visible. These flags require `--engine sat`.

Existence progress and final `meaning.existenceStats` report cube count, inputs per
cube (min/mean/max), whole-program encoded input support size, distinct inputs used
in cubes, and `distinctCubeLiterals` versus `emittedExclusionLiterals`.
`distinctCubeLiterals` sums the widths of distinct cubes, counting a repeated input
once per cube, not once globally. `emittedSelectorLiterals` separately records the
selector overhead. These totals include every component search and any whole-program
fallback. `scopes` gives each cone's component ordinal, position, state, input support
and cube statistics; `componentsTotal` counts negative components, and `fallbackReason`
explains a full-program fallback when upstream is ambiguous. A local ambiguous cone
is an eligibility result, not a global multiple-meaning finding. Component ordinals
identify this prepared residual graph only. No world values are needed for these counters. Progress is
throttled, with an initial sample and a final snapshot, including on exhaustion;
`--no-progress` silences it but keeps final statistics.

`meaning.uniquenessStats` and uniqueness progress report `local-proofs` when completed
cone proofs suffice, or `downstream-cone` for the region that can differ and its
upstream. Component ordinals, encoded atom/input counts, attempted pair/extension
queries and any whole-program fallback reason are included. A scoped pair is extended
and reduct-validated as two full-program models before it becomes a finding.
Skipping existence keeps unclassified negative components in the uniqueness scope;
it never treats them as proved.

Exit codes keep the existing precedence: **2** for incomplete/unanalysed obligations or deliberately skipped meaning,
invalid configuration or a filtered `--verification` run; otherwise **1** for failures
(including empty/inconsistent context or non-unique meaning), **0** for proved,
**3** for operational errors. Known failures remain in an incomplete report.
`--json` retains the usual headers; it is not a bare JSON document.

General grounding/CNF/work/deadline limits apply. SAT-specific options are
`--sat-max-worlds`, `--sat-max-tuples`, `--sat-max-solves`, `--sat-max-refinements`,
`--sat-max-polls`, `--sat-max-conflicts` and `--sat-max-propagations`; see `--help` for
defaults. `--empty-examples` controls retention, not the tuple-checking allowance.
BDD/admission options such as `--checking-within-w`, `--input-order`, `--sat-probe`,
condition profiling and committed-graph export are rejected in SAT mode. No
measurement-only simplification/elimination is applied. Each selected verification
gets its own engine; session/editor integration and cross-verification preparation
reuse are not part of this mode yet.

Detailed progress goes to **stderr** by default, also with `--json`. It reports
effective limits, source inventory, loading and assumption validation, each selected
verification's declarations, preparation/admission/checking/presentation, prepared
sizes, result counts and session reuse. Every phase starts with a flushed line;
transitions report elapsed time. `--no-progress` disables this checker trace.
`--verbose` controls diagnostic detail, independent of progress and checking.

`just check-den <program> --sat-probe` adds a diagnostic search inside admission, after cheap reductions:
does each component with a negative cycle have two stable meanings in a permitted
world? SAT reports a concretely verified pair. After uniqueness UNSAT, a separate
existence search reports `every-world`, `no-meaning` with an input world,
`inconsistent-assumptions`, or `unknown`. Only UNSAT plus `every-world` establishes
exactly one meaning in the probed cone. `--sat-probe-timeout-ms N` (default 10000)
and `--sat-probe-refinements N` (default 64) bound each question independently of
ordinary checking. Unknown includes the stopping reason. Reports appear only in progress
and memory-profile records, including local input tuples and differing atoms with
source locations. Ordinary output and exit codes are unchanged. See the
[probe policy](../../docs/checker-policies.md#diagnostic-sat-probe) for scope and limits.

`just check-den <program> --dump-component FILE` streams bounded, local JSONL
with actual guarded-attempt snapshots and the last committed unresolved graph,
including on admission interruption. Names and locations are resolved by the CLI;
recording cannot change a checker result. See the [dump format and allowances](examples/check/COMPONENT-DUMP.md).

`just check-den <program> --sat-probe-candidates` diagnoses guarded candidates
during admission, independently of the component meaning probe. Progress
reports `ruled-out`, `not-ruled-out`, `unknown` and cumulative unexamined counts.
Defaults are 64 queries, 10 seconds total active probe time and 10 million work
units per admission; adjust `--sat-probe-candidate-limit`,
`--sat-probe-candidate-timeout-ms` and `--sat-probe-candidate-work`. These do not
consume ordinary admission's allowances or change its attempts. A not-ruled-out
candidate is not a proof. See the [candidate policy](../../docs/checker-policies.md#guarded-candidate-filter).

Admission additionally reports rounds, stages, remaining ground components with
negation, blocked atoms and committed rewrites. Upper-bound analysis identifies
its component before work starts, with a representative tuple, source location
and component size. Routine scans/iterations are throttled; exhaustion reports the
precise current work and resource even if its last update was throttled. Reused
admission is labeled `reused`. Counts are snapshots, not percentages or proof
status. This detail is on stderr; `--profile-memory` retains its separate span
and memory format.

Phase boundaries include best-effort process RSS/footprint readings, with OS
lifetime peaks labeled separately. `--profile-memory FILE` creates a new JSON-lines
file with detailed fixed preparation, grounding, graph/component analysis, input-key
ordering, key-index and admission-round events and
20 ms memory samples summarized per span. It also works with `--no-progress`.
The CLI also emits `type: "progress"` records containing the existing structured
phase/admission details, and a `type: "run-end"` record with its exit code/error.
`--profile-conditions` additionally streams `type: "condition-profile"` records:
actual input order (before assumptions), assumption-build checkpoints, retained
conditions of at least 64 nodes at completed component boundaries, and failed
Boolean operations with their operand sizes and current target when available.
These optional records use declaration names and values, add reporting overhead,
and may affect deadline-limited measurements. See the [benchmark guide](examples/schema/README.md#inspecting-knowledge-form-scale)
for aggregation and interpretation. No extra BDD is constructed for observation.
Existing `type: "profile"` fields are unchanged. Post-admission progress carries
updated sizes and remaining negative-component counts. A missing terminal record
means completion was not observed. Unavailable metrics are null; these are process observations, not cache bytes or
per-program allocation totals. See [memory profiling](../../docs/checker-policies.md#memory-profiling)
for metric definitions and `just bench-den-memory` workload controls.

Fixed facts are shared across verifications. The CLI prepares them directly in its
single snapshot; the editor retains a portable session fold across edits.
Residual preparation and admission run once per selected restriction set in a run;
obligation groups, notices and finding identities remain per verification.
Prepared-size output separates fixed present/absent facts, retained original
evidence and the residual executable graph. `fold.retainedBytes` reports the keyed
session fold's accounted bytes (zero for the direct CLI); that single retained
fold has no additional byte cap.
For a generated format tree in Shipping News vocabulary, use `just bench-den-schema`.
It runs the actual CLI with the same optimized build for ordinary and sampled runs,
keeps sources and partial results, and reports sizes before/after admission. See the
[generator's semantics, controls and examples](examples/schema/README.md).

`just bench-den-fixed ITEMS [VERIFICATIONS]`
compares cold and warm folded runs with ordinary preparation on an abstract workload;
the optional verification count defaults to four. `--two-selections` alternates
restriction sets and `--ground-assumption` includes raw-graph validation. An
input-dependent edit measures fold reuse. `--no-retention` measures direct fixed
preparation without reconstructing/exporting a retained value. Measurements are not goldens.

The CLI and LSP share `progress::CheckProgress` and `Phase`: identical phase names,
verification metadata and prepared sizes. Delivery remains with each frontend.
Counts describe completed preparation, not an estimate of checking work remaining.
After admission, stderr lists each remaining negative component's size and up to
12 edges of its representative cycle, with current source locations and any
admission exhaustion. These are structural observations, not no-meaning findings.
During checking, it names the current obligation, notice or component and work such
as symbolic evaluation, replay, certification and attribution. Exhaustion is
reported immediately when detected or recovered from cache, including the resource,
limit and observed demand when available, and whether other checking work continues.
Notices and optional attribution can recover from deadlines; a checking deadline
otherwise stops the verification. Inner traversal is sampled, not a heartbeat
inside an individual BDD operation. There are no live BDD node counts.

Completed verification reports are flushed to stdout before the next verification,
including in `--json` mode and when later work fails. Concatenated stdout and exit
policy are unchanged. Individual tentative findings are not streamed. Progress
never runs an additional check, changes a semantic budget or enters a cache key.

All public `Limits` resource ceilings are configurable for this invocation:
`--max-atoms`, `--max-rules`, `--max-dependencies`, `--max-work`,
`--max-bdd-variables`, `--max-bdd-nodes`, `--max-bdd-tasks`, and
`--max-condition-nodes`, plus `--timeout-ms`. Structural splitting also exposes
`--max-structural-split-depth`, `--max-structural-split-leaves` and
`--max-structural-split-work`. `--max-structural-split-scoring-work` controls the
per-node scoring allowance (default 1,000,000): stop further scoring between
complete scores and keep the best improving choice; one score can cross it. Zero
disables scoring. It reserves no work for leaves. The other three controls apply
per component attempt: exhausting one
falls back to ordinary admission, while global work and deadlines still apply.
Raise leaves alongside depth when exploring deeper trees (a one-sided path of
N splits has N+1 leaves); raising only depth may just hit the leaf cap.
Values are nonnegative integers; zero allows no use of that resource. `--help` lists the actual default values.
Limits remain per operation/query; the cooperative timeout is not a total command
deadline and does not cover loading or presentation. Exhaustion of required work
remains explicit inconclusive, with the existing exit-code policy; optional split
exhaustion reports its fallback in progress. Cache-retention policies and
separate diagnostic attribution allowances are unchanged.

`--checking-within-w` opts in to evaluating verification conditions within the
selected assumptions. It can greatly reduce conditions for mutually exclusive
alternatives, but increase storage for independent input groups. Default checking
remains unrestricted. It does not change admission, assumption construction or
limits; API callers set `CheckRequest::checking_within_w`.

`--empty-examples N` retains a positive number of examples per emptiness obligation
(default three); `--empty-examples all` retains every confirmed tuple, including in
JSON summaries. Counts remain lower bounds if checking is incomplete. It does not
change verdicts or exit-code policy, and it does not enumerate alternative
derivations or worlds for the same tuple.

`--hide-library-rewrites` hides diagnostics for rewritten rules owned by included
libraries, with a count of hidden findings per verification. Own-file rewrites and
all other diagnostics remain visible. The full finding inventory stays in the
status summary, including with `--json`, and exit codes stay unchanged. The shared
view filter is `Presentation::hide_library_rewrites`; it checks rule ownership,
not where a diagnostic happened to be placed.
See the [command contract](../../docs/den-format.md#commands) for ordering and exit codes.

The round trip of the test DSL
regression programs through printing and loading lives in
`crates/test-dsl/tests/ir_text_roundtrip.rs`.

Selected contextual condition notices load and print as ordinary IR declarations:
`notice n: varies(condition, within: scope);` and the optional verification field
`notices: [n];`. Both relations are zero-arity; omitting `within` means the full
permitted context. Origins and the shared editor resolver apply normally. CLI human
output includes advisory diagnostics, including Information when a selected condition
could not be analysed (unsupported dependencies or exhausted limits/deadlines).
JSON also includes quiet notice results. Inconsistent contexts keep only their context
Error; notice findings do not change exit codes.
Notice outcomes do not change exit codes. See the
[format documentation](../../docs/den-format.md#contextual-condition-notices).

## Whole-program CNF measurements

```sh
just measure-den-cnf ROOT --eliminate
```

This size-only experiment emits JSON with before/after variable, clause and literal
occurrence counts; before/after-elimination counts and payload bytes by relation; vector storage and separate
reconstruction storage; fixed/residual sizes; and loading, preparation and encoding
times. It encodes the whole residual completion and declared input cardinality U,
without selected assumptions, global BDD construction, admission or checking verdicts.
It works with a discovered `den.root` closure, including library declarations.

`--max-atoms`, `--max-rules`, `--max-dependencies`, `--max-work`, and `--timeout-ms`
use checker defaults. Encoding uses those size limits for variables, clauses and
literal occurrences respectively. Preparation and measurement have separate budgets.
A globally exhausted phase exits 2 with an error, without a successful report.

`--eliminate` compares bounded CNF resolution with the original encoding; inputs
and recursive atoms remain protected. Storage counts cover named vector capacities,
not total memory, allocator overhead, preprocessing scratch, peak RSS, or a SAT
solver's storage. Reconstruction adds retained memory even when the final CNF shrinks.
The command does not claim that its completion models are stable models.


Add `--simplify` to compare eight variants: baseline, baseline plus elimination,
each of four independent passes (structural hashing, constants, dead bodies and
redundant premises, syntactic subsumption), all passes, and all plus elimination.
This includes both elimination controls whether or not `--eliminate` is supplied.
Each variant has its own global measurement allowance and reports per-pass time,
proved/unchanged/cut-off candidates, skipped recursive heads, and CNF size by relation.
The JSON also reports working-model vector bytes (including the alias table), the
alias-table subset separately, and retained rewrite-record bytes. Variants are
measured sequentially; their storage figures are not added together as peak memory.

Local U-only BDD proofs are bounded by `--local-cone-atoms` (default 64, including
added input-group members), `--local-bdd-nodes` (4,096 cumulative created nodes per
proof, including clones), and `--local-work` (50,000 per proof). Subsumption uses
the work allowance per head. Cut points are free variables, and input-cardinality
groups are included whole or omitted conservatively. A local cutoff skips that
candidate, with a counter in the report. This experiment does not change ordinary
checking, selected assumptions or input variable identities.

Every report includes `recursive_components` for the original residual graph after
fixed preparation, before simplification: positive/negative component counts, atom
and rule-instance totals, largest sizes, exact atom-size histograms and counts above
100 atoms, plus each component's relation membership. Component indices identify
this report's graph only. Component reporting and paired-proof comparison have
separate elapsed fields; their time is excluded from encoding/elimination time.

To diagnose a lost local proof with a larger cone, without changing the defaults:

```sh
just measure-den-cnf ROOT --compare-local-limits 256,65536,100000
```

The triple is cone atoms, cumulative created BDD nodes and work per proof. The base
uses the existing `--local-*` options (or their defaults). `local_proof_comparison`
reports the first base proof not reproduced with the comparison limits: its head,
body/premise, cone sizes, cut points, groups, work, created nodes and cutoff reason.
Both proofs see the same original acyclic snapshot; no rewriting occurs between
them. A null `first_lost_proof` means this scan found none, not that two sequential
simplification runs must agree. Larger cones can replace cheap free cut points with
expensive definitions and exhaust even a larger allowance. The scan has its own
global measurement budget, and aborts on global exhaustion as other measurements do.
The report contains program names and values; keep private-program reports local.


SAT preparation propagates independently settled ground atoms before meaning checks.
Its automatic `subsumed-producer` Information diagnostics identify redundant source
rules, with affected tuples and supporting rule locations. They use the shared
notice placement path, preserve original provenance, and never change exit codes.
They are distinct from declared condition notices, which SAT still does not analyse.
JSON exposes diagnostic-work exhaustion as `subsumptionIncomplete`; the default BDD
and editor paths do not yet publish these automatic notices.

SAT preparation also drops syntactically subsumed same-head producers, including
duplicates, and reports their original supporting rule through the same Information
notice. No selected assumptions or semantic implication queries justify this pass.

Before checking, SAT output lists the remaining negative components, their atom and
relation counts, and signed sample cycles with rule source locations. This also
works with `--sat-meaning none`. JSON has a `Negative components:` inventory with
`total`, `components`, `complete` and a truncation `reason`; each component carries
`atoms`, `relations`, `cycle`, `cycleSearchComplete` and `omittedEdges`. A cycle edge carries `consumer`,
`provider`, `polarity`, and its original rule's `source` (URI and one-based scalar
line/column, or null). The inventory is structural, not a no-meaning finding.
`--dump-component FILE` additionally writes bounded JSONL atoms and rules for this
SAT view (`state: sat-prepared`). Dump or inventory truncation never changes exit
status. BDD's existing dump behavior is unchanged.


### Completion verification from the CLI

`just check-den ROOT --engine sat` also runs authored `semantics: completion`
verifications. Full meaning analysis is required; `--sat-meaning cone`,
`uniqueness`, `none`, and explicit split hints are refused for these verifications.
Stable verifications in the same program keep their existing path. Completion runs
retain program-wide assumption declaration validation, including unselected ones.

Human and `--json` output identify the semantics and hypothesis, classification
acceptance/rejection/ambiguity/no-meaning, the declared determinacy interface,
processing meaning, properties and advisory status. Classification no-meaning is a
specification failure even when rejection is allowed: a genuine reject needs an
interpretation of the original classification cone without H and none with H.
Rejection evidence retains that checked interpretation and the unsatisfiable-query
confirmation. All-rejected excludes classification no-meaning and unknowns.
The configuration is `original-completion-v1`. Rejections are allowed unless selected
`no_rejections(H)` forbids them. Fully established `all-rejected` is explicit,
processing is not applicable, and processing obligations are vacuous. It can exit 0;
there is no unqualified program proof. Required unknown/unanalysed work has exit 2,
which takes precedence over a known failure (exit 1). Partial selection stays exit 2.

The existing SAT solve/world/tuple/CNF limits bound this completion path.
Grounding joins greatest-fixpoint possible tuples, preserving unseeded recursion
and original classification scopes. Whole-verification checks use symbolic pair
queries and generalized input cubes. `--sat-max-worlds` bounds candidate observations
per search, not the number of concrete observations covered by a cube. Dense
possible relations or difficult existence searches can still exhaust limits. Empty and at-most-one are supported, with
coverage/exactly-one for acyclic input-independent cones; symbolic coverage and
notices remain explicitly unanalysed. Completion property evidence includes checked
interpretations and scope, without fabricated finite derivations. Placement falls
back to the obligation, retaining labeled library fallbacks and upstream origins.

`--completion-circular-support` opts into an advisory on accepted classifications
that require positive circular support. It is off by default, uses separate limits,
and cannot change exit codes even when detection is incomplete. It does not apply
to stable verifications. BDD/editor/planner/scorecard completion checking remains
unsupported.
