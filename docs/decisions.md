# Decisions

Settled design choices and why they were made. Current behavior is specified in the
[`.den` format](den-format.md), the [architecture](architecture.md) and the
[editor protocol](../crates/den-lsp/PROTOCOL.md); this page records the reasons and the
alternatives that were rejected. Revisit a decision only with new evidence, such as a
real program that the current choice serves badly.

## Meaning and checking

- **Input domains define the universe; assumptions constrain its worlds.** A
  restricted input names an input-free, stratified derived provider. We evaluate
  that provider exactly before grounding inputs, independently of verifications,
  over the checked program's closure and resolved sort domains. Using the possible
  grounding closure would wrongly include tuples excluded by negation; using a
  partial evaluation after exhaustion could hide real counterexamples. Preparation
  therefore fails inconclusively as a whole when domain evaluation exhausts its
  limits. Input eligibility alone still permits the all-absent assignment, but an
  empty provider can make uniqueness or emptiness trivially true; coverage continues to enumerate
  groups from sort domains. A sort-correct excluded atom is false in rule bodies,
  and invalid as a supplied present observation. Observation lists omit it.
  This is an explicit declaration constraint, not an imported implicit assumption
  ([syntax and meaning](den-format.md#restricted-input-domains)).

- **Assumptions stay named and selected; all four cardinality forms are supported.**
  Trusted library contracts can constrain independently stratified input-dependent
  relations. Global activation would silently change a consumer's declared context;
  library verifications instead select reusable assumptions over consumer metadata.
  Restricting the new vocabulary to `empty` would make authors encode ordinary
  cardinality contracts indirectly. We therefore allow `empty`, `at_most_one`,
  `at_least_one` and `exactly_one`, with the same grouping domains as obligations.
  Constraint meaning is computed before assumption-based admission, with no cycle
  through negation in a constraint cone. A real consistency check prevents vacuous
  proofs; exhaustion cannot discard constraints. No unsatisfiable-core explanation
  is attempted yet. A directional warning catches assumptions of a checked conclusion
  without warning on ordinary assume-guarantee use. Sharing a derived intermediate
  alone is not enough to warn, because it is common in valid assume-guarantee models.

- **Ordinary rule negation is admitted by justification, not by stratification.**
  Business DSLs naturally define mutually exclusive cases that negate each other. Relation-level
  stratification would reject them, so the checker proves such negations redundant
  under the assumptions, or certifies a world, and reports everything else as
  unsupported or no-meaning ([meaning](den-format.md#meaning)).
  The well-founded semantics is not adopted until a real program needs it.
- **Conclusive answers must be sound.** A false counterexample or a silent success
  misleads the author; an explicit inconclusive or unsupported outcome does not. Hence
  counterexamples only after concrete replay (or certification); blocked or unknown
  facts are never evidence of absence.
- **BDD is the only backend.** The SAT experiment had synthetic/test-DSL performance
  wins but no demonstrated need on real programs. It increased implementation and test
  work for every obligation kind and made diagnostics depend on a setting. We retired
  it before extending the vocabulary further. Reintroduce an alternative only for a
  real program that exhausts BDD evaluation within reasonable limits, re-scored with
  the `.den` scorecard (a prerequisite still on the roadmap), with better conclusive
  outcomes under comparable limits and agreement with the independent semantic oracles.
  The existing protocol backend/configuration identity remains fixed BDD metadata for
  result validation and compatibility; it is not a user-selectable option.
- **Assumptions take effect only through an explicit verification.** Assumptions are
  the domain constraints a library author chooses. When every declared assumption was
  active, declaring or importing one silently changed every check, and one obligation
  could not be checked under two sets of assumptions. A verification names its
  context, so the author's choice is visible and the same obligation can be checked
  under several contexts.
- **No verification, no semantic checking.** Any implicit context (unrestricted inputs,
  or all assumptions) would be a choice the author never made, and could report a
  library as wrong, or as proved, for inputs it was never meant to accept. The
  editor and `check-den` say "unconfigured" instead.
- **Analysis is per verification.** Admission, rewrite proofs and no-meaning findings
  depend on the permitted worlds, so they are computed for each verification, never
  once for the program and reused. Finding identities include the verification, so
  two verifications of one obligation never overwrite or deduplicate each other.
- **Coverage ranges over resolved domains.** Enumerating only groups with producing
  tuples would silently miss missing assignments. `at_least_one` therefore includes
  all grouping-domain combinations, including overrides. Enumeration is bounded;
  exhaustion remains explicit, with known failures preserved. An empty grouping
  domain proves coverage vacuously but gets an Information note to expose accidental
  empty scope. Empty grouping itself still creates one global group.
- **Coverage failures are aggregated; uniqueness failures remain per group.** One
  diagnostic per missing domain combination could flood an obligation declaration.
  Coverage therefore retains a bounded sample and an exact count or explicit lower
  bound. Its identity depends on the obligation, component and verification, never
  on sample selection. Each example retains its own input world.
- **Exactly one is one declaration with independent parts.** Splitting it into hidden
  authored obligations would complicate selection, rename and source identity. Instead,
  the same obligation runs coverage and uniqueness under the same selected assumptions;
  neither part constrains the other. Component identities keep both findings visible,
  and a failure survives an inconclusive result in the other part. Existing standalone
  coverage and uniqueness identities remain unchanged.
- **Emptiness is ungrouped and requires replayed presence to fail.** `empty(R)` has
  no grouping argument and one result per obligation/verification. Its finding identity
  uses component `emptiness`, independent of the selected example tuple or world.
  Unknown facts are neither presence nor proof of emptiness. A replayed failure is
  retained alongside unresolved analysis. Like coverage, it reuses session preparation
  but recomputes its verdict under bounded work rather than adding a verdict cache.
- **Emptiness placement follows its retained derivation, as uniqueness does.** A
  replayed present tuple already has grounded support, so use its producing rules
  and facts instead of introducing author syntax for diagnostic targets. Certified
  presence uses the certified derivation. One derivation per tuple is retained;
  placement may depend on that choice, but finding identity does not. Attribution
  runs after semantic checking under a fresh bounded allowance; exhaustion is
  reported separately and falls back to the obligation without changing the verdict
  or semantic completeness. Explicit diagnostic targets remain deferred.
- **Library counterexamples stop at the first consumer producers.** Traversing the
  retained proof's positive support gives a useful ownership frontier without
  author syntax: the consumer rule or fact that supplies the library's result is
  primary, while its guards and supporting declarations stay related. Traverse
  unlocated generated rules and the full transitive library closure; declaration
  or literal locations cannot stop the walk. Deduplicate shared support rather than
  enumerating proof paths. Union frontiers per reported tuple and preserve each
  tuple's fallback independently. Locally authored obligations keep their existing
  detail; unknown ownership also keeps existing placement. This is presentation
  over the same proof, with no new checker policy, evidence or attribution budget.
- **Several emptiness examples belong to one finding.** Independent invalid tuples
  should be visible together, without changing the obligation/verification identity
  when an author fixes one. Retain up to three confirmed tuples in semantic-key
  order, each with its own world, replay scope and bounded attribution. Count
  distinct tuples across worlds, exactly when checking completes and as a lower
  bound otherwise. Keep the semantic scan order and its existing work charges;
  sample retention does not spend the semantic allowance. Attribute each retained
  tuple after checking with a fresh allowance, then union its locations and label
  them with the tuple. Per-tuple identities are deferred until suppressions, waivers
  or another consumer needs to track individual errors; introducing them now would
  add identity and publication machinery without a consumer.
- **Obligation world notes use structural input cones.** Filtering to retained proof
  leaves hides inputs behind negative derived premises: `violation() :- order(),
  !approved(); approved() :- signed();` still depends on `signed()`. The checker
  collects each retained tuple's ground dependency-cone inputs, including alternative
  producers, after semantic checking under a separate bounded allowance. Uniqueness
  uses the union for its conflicting tuples; coverage uses all candidates of the
  missing group, since there is no present violating tuple. Session
  projection uses semantic keys; presentation only restricts the observation to that
  supplied scope. Empty cones omit the note; unavailable cones explicitly fall back
  to the full world. The complete replay witness remains in structured evidence.
- **Coverage failures point to the missing group's authored constants.** A missing
  tuple has no derivation to blame, but its grouping constants are already in the
  checked evidence. Their locatable current declarations in the program's own files
  provide useful primary locations without new syntax or checker work; the obligation
  becomes related. Union retained examples and merge notes at shared locations.
  A group with no qualifying declaration keeps obligation placement, including
  library fallback: neither library-only constants nor upstream origins should
  displace it. Multiple diagnostics still represent one coverage finding per
  obligation and verification. This is placement, not a change to group eligibility
  or an explanation of why no tuple was derived.
- **Correctness and usability before performance.** Performance policies are
  provisional until re-scored on real programs ([checker policies](checker-policies.md)).
- **Budgets, receipts, timings and witness choices are not goldens.** They change
  whenever a provisional policy changes. Tests compare outcomes, identities,
  diagnostics and cold/warm equality.

- **Contextual condition notices are selected advisory queries.** `notice n:
  varies(condition, within: scope)` references zero-arity relations and is selected
  separately from obligations. A reachable parent with only a false condition gives
  Warning; one with only a true condition gives Information. Both reachable sides
  require replayed witnesses. An unreachable parent suppresses child noise, and
  unsupported or incomplete meaning stays unknown. Inconsistent assumptions never
  produce notices by vacuity. The author supplies the complete enclosing scope;
  conclusions and siblings are not implicit assumptions. This keeps contextual
  authoring advice out of business-rule verdicts and avoids DSL-specific metadata
  interpretation in the checker. Each notice gets an independent bounded query after
  ordinary checking; exhaustion cannot change obligation results. Results use stable
  notice/verification keys. The current implementation recomputes notice queries in
  warm sessions; no cached result may capture stale source locations. Full worlds
  stay in evidence, declaration origins support source-use placement, and no automatic
  rewrites or formula interning are implied.

## The `.den` format

- **`.den` is both an authoring and an export format**, MLIR-style: plain files with
  embedded `loc(...)` origins that reload into the same program.
- **C#-style namespaces, independent of files.** Nested, reopenable, spanning files;
  `use` is visibility only. Qualified paths are absolute; inner names do not shadow
  outer ones (ambiguity is an error). Relaxing shadowing later would be compatible;
  relative paths would not, so they were rejected.
- **No `order N`.** Cross-file rule interleaving has no meaning and is not transported.
- **Identity is independent of files and positions**, so moving, reformatting or
  splitting files does not change cached results or finding identities.
- **Origins identify sources by content** (URI, view, SHA-256), so a changed source is
  detected rather than navigated to the wrong place.

## Programs and roots

- **`den.root` JSON manifests define programs.** Kept as JSON rather than `.den` syntax
  to keep membership separate from program text.
- **No implicit roots.** A workspace-folder root would exist only in the editor, so the
  editor and `check-den` would check different programs. A file outside every
  `den.root` is a standalone program instead, with a quick fix to create a root.
- **Every program is checked; there is no "active root" selection.** Because scanning
  stops at nested roots, each file already has exactly one owning root, its home
  program. A selection could only choose which consumer's results a shared library
  file displays, making its diagnostics depend on hidden per-document state that every
  switch would withdraw and republish. Instead each consumer's results appear on its
  own files, and the library file shows the library checked alone. This replaced an
  earlier design with an explicitly selected active root per document.
- **Included verifications run in every consumer; consumers only add.** A library's
  verification states a contract that each consumer must meet with its own facts, so
  it runs in every program that includes it and cannot be overridden or weakened by
  a consumer, which may only add verifications of its own.
- **Unchecked obligations are noticed, including in libraries.** Moving from implicit
  to explicit selection creates a new silent failure: an obligation nothing checks.
  Each program reports every obligation in its closure that no verification selects,
  at the declaration (through the labeled fallback for library files), as information
  rather than as a finding.
- **A finding belongs to the program whose check produced it.** When a consumer's
  finding involves none of its own files, it is published on the library location,
  labeled with the consumer, rather than lost; it is not deduplicated, because each
  consumer checks the library under its own facts and assumptions. Likewise a consumer
  declaration that makes a library name ambiguous is reported on the consumer, since
  the library checked alone has no such failure.

## The editor

- **Warm sessions survive temporary breakage.** A program with a syntax error is
  blocked but keeps its checker session, so typing does not cost a cold check; only
  removing the root releases it.
- **Rename is validated by re-resolving, not by a reference list.** A dry run over
  every affected program catches capture, new ambiguity and structural changes that a
  list of references cannot.
