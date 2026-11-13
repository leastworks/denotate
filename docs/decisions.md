# Decisions

Settled design choices and why they were made. Current behavior is specified in the
[`.den` format](den-format.md), the [architecture](architecture.md) and the
[editor protocol](../crates/den-lsp/PROTOCOL.md); this page records the reasons and the
alternatives that were rejected. Revisit a decision only with new evidence, such as a
real program that the current choice serves badly.

## Measurement

- **Show direct structural justification; expand chains on request.** A source
  warning can group thousands of ground proofs sharing a long settling chain.
  Traversing that chain for every proof, then resolving repeated source locations,
  made presentation dominate a production run. Default warnings show the immediate
  justification, including settled premises used by subsumption and accurate
  absence reasons. Bound the union per source warning and disclose omissions;
  retain full certificates for explicit verbose expansion. Internal structural
  evidence keys use direct support, while local cache inputs retain the full
  original dependency closure. All diagnostic identities, checker proofs and
  limits stay unchanged. Snapshot-local coordinate/hash indexes avoid rescanning
  the whole source for each displayed location without using newer buffer text.

- **Measure process memory separately from retained payload.** Cache accounting
  cannot explain a process killed during admission. Phase observations distinguish
  RSS, physical footprint, lifetime peaks and sampled span peaks. Optional checker
  profile events carry no semantic inputs and perform no OS reads; drivers own
  sampling and delivery. BDD result-node traffic and deduplicated retained node
  payload are labeled separately from allocator traffic. Profile through semantic
  indexing and admission refresh before choosing a representation or backend
  change; a large fixed graph alone does not establish the cause of a later peak.

- **Project ground keys on demand instead of duplicating the ground program.**
  Production profiling attributed the largest growth to keyed copies of original
  and committed rule bodies, followed by another complete index during admission.
  Share source schemas and bindings, and read the existing graph's original rules
  and admission changes when a query, replay or finding needs keyed content.
  Cross-edit query inputs still include complete relevant structure, not just rule
  identity. This removes index duplication without changing admission, the BDD
  backend, or the fixed evidence graph. Measure through checking and presentation
  so deferred work cannot hide a later memory peak.
- **Use direct fixed preparation for the one-shot CLI.** `check-den` shares work
  across verifications in one snapshot but has no later snapshot to reuse a
  portable fold. Avoid its reconstruction, export and rebinding there; keep session
  retention for editors. Limits remain unchanged; transfer receipts and valid
  witness choices may differ between direct and retained preparation.

## Meaning and checking

- **Replace cyclic premises only with a guard-relative, non-circular certificate.**
  A premise need not be always false to cut its cycle edge. Under a rule's settled
  guard G, it may equal an input-dependent expression over globally settled atoms.
  For example, under `!perishable`, `claim_fails :- docked, !reefer_booked` can
  equal `docked` when every producer of `reefer_booked` requires `perishable`.
  Replace the signed premise by that expression while retaining the reading
  rule's guard. Store one bounded Boolean expression on the ground rule rather
  than distributing negative formulas into rule variants. This avoids branch
  growth and preserves the authored rule and occurrence identities.

  The certificate starts with atoms whose descending upper bounds are false
  under G. Further atoms are marked only when all live producers depend on
  earlier marks and globally settled facts; unresolved external providers stay
  unknown. The reading producer is never a live producer of its own certificate.
  Bounds used here relax that producer to G and exclude it from exact guarantees.
  This is essential: bounds must survive the replacement, rather than rely on
  the very cyclic premise being removed. One replacement per component is committed
  per snapshot; independent components can share the atomic batch.

  For supported models in either graph, the relaxed operator bounds the component
  because the reading producer can imply no more than G. By induction on the
  certificate ranks, every marked atom therefore equals its expression in either
  graph whenever G holds. Outside G the changed rule is dead. The original and
  rewritten rule consequently accept the same supported models.
  For stable models, globally settled facts have finite derivations independent
  of the unresolved component. Each positive mark that is true expands into a
  finite derivation through earlier marks; false marks have no live producer.
  With negative premises fixed by a candidate model, these expansions preserve
  the least reduct model in both directions. No support can be supplied by the
  changed rule itself. This excludes the unsound unfolding of `h :- !p; p :- !h`
  into `h :- h; p :- !h`, which loses a stable model despite preserving supported
  models. Exhaustive stable and supported-model oracles cover both directions.

  **Guarded bounds run in their own domain and live cone.** Conjoin the retained
  guard with W before iterating. The upper-bound operator is pointwise: starting
  from G ∧ W, and masking every producer and exact guarantee to that domain,
  gives the unrestricted candidate-relaxed bounds conjoined with G ∧ W at every
  iteration and at the fixed point. Comparisons use ordinary Boolean difference;
  no care-set simplification changes values outside the domain. A distinct
  `GuardedBounds` certificate carries that domain and cannot be passed to the
  unrestricted removal/discharge path.

  Follow dependencies backward from the candidate premise, dropping a producer's
  edges only when its settled condition is false under G ∧ W. The reading
  producer is relaxed before traversal: keep its guard, omit its cyclic premises,
  exclude it from exact guarantees and never use it as a live settling producer.
  This pruning remains valid after replacement. The retained cone is closed under
  the relaxed operator's dependencies, so its bounds equal the full component's
  restricted bounds. Dead producers remain certificate evidence; unresolved
  external producers remain unknown. The supported/stable-model argument above
  therefore applies unchanged.

  Preprocessing is charged and lazy. Informative guards precede unrestricted ones;
  smaller guard representations and immediate producer counts estimate cost,
  with stable original-order ties. One snapshot-local cache entry retains the
  latest bounds or failed computation's key. A hit requires identical domain,
  component, cone, snapshot and relaxed rule; the relaxed rule is irrelevant only
  when its head is outside the cone. Different representations may miss a hit,
  never invent one. There is no broad-to-narrow failure inference. One entry
  bounds optional reuse's retention without introducing another tuning limit;
  metadata and conditions count against storage/work allowances. If cone preparation
  hits storage pressure, release the optional entry and retry once with the same
  cap; only a repeated failure becomes a skip. It is also released at replacement
  or end of the snapshot. Work already spent remains charged.

  Existing producer removal and negation discharge get the first opportunity;
  guarded settlement runs only when they have no batch. This deliberately preserves
  established discharge warnings and their failure-local attempts. Bounds and
  settlement have separate attempt identities. A replacement conservatively
  invalidates all invocation-local failed/negative attempts; subsequent ordinary
  commits track expression leaves as settled dependencies. Replay, completion,
  certification and keyed local queries execute the same attached expression.
  The certificate stays separate from the executable condition and points back
  to original source. New `guarded-settlement` warnings describe an equivalence,
  not redundancy; they are advisory for CLI exit codes. Existing warning behavior
  and finding identities are unchanged. Display is bounded, with full steps on
  request; no source edit is authorized.

- **Strengthen cycle bounds with independent exact guarantees.** A cyclic
  producer can require a condition implied by another producer only after
  following several positive and negative dependencies. After cheap removals,
  union the exact producers for each atom into a lower guarantee and descend
  upper bounds from true, using the complement of that guarantee for internal
  negative premises. Remove a non-exact producer only when its body's upper
  bound implies the head's exact cover under the selected assumptions. Bounds
  remain proof metadata; they never settle executable atoms. Recursive lower
  coverage and well-founded bounds are deliberately excluded.

  Soundness must hold in both directions. All guarantees and covering producers
  have settled premises, independent of the blocked component, and stay present
  throughout the batch. Consequently the same descending operator bounds the
  unresolved part of every supported model of both the original graph and any
  graph with this batch removed. Unknown external premises are relaxed, never
  treated as absent. A deleted body's truth therefore implies a retained cover
  in either graph: deletion loses no supported model and creates none. For stable
  models, that cover has a finite derivation through the settled upstream graph.
  In the original model's reduct, any use of a deleted producer can be replaced
  by that independent derivation, preserving the least model. Conversely a stable
  model after deletion satisfies the deleted rules via the same cover; adding
  those rules back cannot change its least reduct model. All reasoning is within
  the selected world's assumptions and the existing settled meanings.

  Reusing a recursive alternative as lower cover would invalidate that argument:
  in `a :- !i, !b; a :- c; c :- a; b :- a, i`, with `i` absent, removing the first
  rule changes the stable model from `{a,c}` to `{}`. Exact-only cover prevents
  such circular support. Independent stable/supported-model oracles check the
  new pass, including this counterexample and the two-step removal pattern.
  Bound attempts have separate skip identities and conservative dependency-cone
  invalidation: even a change confined to blocked premises can tighten a bound.
  Certificates retain the bounds, exact guarantees and producer summaries;
  default warnings show the direct cover, with bounded details and full expansion
  on request. Public finding identities and existing proof keys do not change.

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
- **Commit independent producer coverage before analysing remaining cycles.** An
  atom in a negative component can already have an independently settled producer
  covering every case in which its cyclic alternative could apply. Previously that
  alternative's removal waited in a batch while bounds were computed for the same,
  unreduced component; exhaustion could discard the available proof. Admission now
  commits producer removals first, rebuilds components and repeats before attempting
  negation discharge. Exact coverage under the selected assumptions remains the
  justification, and original rules and replay evidence remain available. This is
  an ordering change, not structural body subsumption or a new meaning for unresolved
  atoms. Extra snapshots and changed proof choices are possible; limits stay explicit.
- **Reuse exact producer coverage only within its admission snapshot.** Non-exact
  removal candidates for one head all compare against the same exact producers.
  Rebuilding their disjunction for each candidate repeats potentially expensive BDD
  work. Compute it lazily, retain it only through that head's last candidate, and
  count the retained condition against the existing storage allowance. Keep the
  original candidate and producer order, proof contents and transactional commits.
  This does not change the symbolic fold, upper bounds or rewrite policy. Covering
  producer summaries are still cloned per successful proof; reducing that separate
  evidence cost requires a later change.
- **Reduce structure before asking BDDs to prove redundancy.** Admission first
  propagates structural truth and falsity, removes dead alternatives, and compares
  signed bodies after bounded unfolding of single-producer positive premises.
  A true producer has a finite settling chain; its alternatives add no result.
  With no live producer a non-input atom is false, so positive consumers cannot
  fire and negative consumers are satisfied. Existing concrete evaluation supplies
  input-free settled boundaries; the pass adds no inference about unseeded cycles
  in blocked regions. These deductions preserve every stable model of the
  current snapshot, not just one chosen observation.
  For subsumption, positive unfolding substitutes a unique producer's body.
  Closure and support give equivalence in each stable model; the terminating
  positive expansion also preserves finite derivations in its reduct. A producer
  requiring a superset of a retained producer's signed premises therefore adds
  neither a model nor support. Negative premises, inputs, multiple producers and
  cyclic expansion are boundaries. Equal bodies retain a deterministic survivor;
  mutually dependent proposed deletions cannot delete every duplicate.
  Structural deletions are sequentially justified inside one private worklist and
  committed transactionally before symbolic evaluation. Later rounds inherit any
  earlier assumption-dependent rewrites; the pass makes no new use of assumptions
  or Boolean conditions. Its flat, shared certificates retain settling and
  unfolding sources without copying a long chain into each warning. Original
  rules remain available to replay and local query construction. The fixed fold's
  original-cycle and assumption-validation policies are unchanged.
  This increment removes rules only in blocked regions. Settled producers still
  supply truth and unfolding evidence, but do not gain new warnings: folding has
  already taken them out of execution on the session path. Whole-program shadowing
  warnings would require a separate pass over the retained fixed graph. Supporting
  source chains and their location order agree on folded and unfolded paths.
- **Cycle-relevant admission precedes downstream rewrites.** Negative components
  and their blocked provider cones receive structural reduction, producer-removal
  proofs and discharge before downstream proof/evaluation work. A wide consumer
  cannot consume the proof budget before a small cycle that would settle it.
  Supporting settled producers remain available; whole-program graph maintenance
  and the full input universe remain necessary shared work. Proof rules and
  transactional commits are unchanged. Downstream work still checks blocked heads
  and assumption-dependent input negations on settled rules. It may produce fewer
  warnings when previously blocked producers become exact; preserving all earlier
  warnings would require a separate lint policy. Logical downstream exhaustion is
  advisory, recorded separately from admission limits and displayed at the
  verification. It cannot relabel phase A's admitted or unsupported regions. The
  graph, marker and logical receipt are reusable together at the same limits;
  cancellation/deadlines remain operational aborts and are not reused.

- **An expensive admission proof does not stop independent proofs.** A per-operation
  BDD task or result-node failure inside coverage, a removal check, component bounds
  or a discharge check skips that attempt. Partial batches remain sound: each proof
  uses one immutable snapshot, removals never remove the exact producers covering
  them, and a discharge does not assume another proposed rewrite. A skip adds no
  rewrite. Temporary bound computations (including guarded-cone preparation)
  also skip on retained-condition storage exhaustion: their partial values are
  dropped and their storage accounting restored before continuing. This lets a
  small guarded certificate run after an unrestricted bound exceeded storage.
  Limits are unchanged; successful certificates, shared values and cache entries
  still count against them. Other retained-storage failures, global work,
  deadlines, cancellation and failures in shared evaluation/summaries stop the current phase and discard the pending batch;
  downstream exhaustion is recorded separately as above.
  Failed preflights consume their task allowance plus one stopping step; a preflight
  constrained by remaining work (including a tie with the task cap) reports global
  work exhaustion. Bounds and discharge retries follow both signs of dependencies
  from changed producer heads through the pre-commit graph, including old SCC members.
  Current skips accompany reused admission and explain only their own unresolved
  components; a downstream skip cannot label an upstream cycle as exhausted.
- **Retry coverage and removal only when their summary inputs can change.**
  A rewrite preserves meaning under the selected assumptions W, but can change
  unrestricted conditions outside W (for example, dropping `!value(b)` from
  `value(a), !value(b)` when W forbids both). An already settled atom has no blocked
  dependency. Changes inside blocked regions therefore cannot change its condition:
  they can only settle more atoms. Changes to already settled producer heads can
  affect conditions throughout their reader cone, through either polarity.
  After each tentative graph rebuild, compare exact-producer membership and the
  settled premises of their current bodies. Also check whether those premises
  depend on a rewritten, previously settled head. Removal retries additionally
  compare the candidate's own settled premises. Rule identity alone is insufficient:
  an exact producer on a blocked head can lose an input guard without changing ID.
  Settled premises entering a summary always invalidate it; changes confined to
  premises that remain blocked do not. Obsolete attempts are discarded.
  The input universe, order, W and operation limits remain fixed during admission;
  rewrites change bodies and edges, never inputs or their prepared key order.
  Identical ordered operands therefore give the same BDD operation, with an equal
  or smaller remaining-work preflight allowance. Repeating a local failure adds
  nothing. A defensive input/order comparison invalidates every skip if a future
  rebuild changes this invariant. No BDD fingerprints or cross-run cache are used.
  Bounds and discharge retain conservative invalidation. Retry analysis is charged
  and finishes before committing either the graph or the retry state.
- **Remember completed negative admission proofs within an invocation.** A proof
  attempt that found no justification need not repeat after an unrelated rewrite.
  Removal, bound-removal and discharge cache only that outcome and the stable
  ground attempt identity; they use the existing skip invalidation, including
  unrestricted settled-condition changes under assumption-relative rewrites.
  Bounds and discharge remain conservative across either sign of dependency and
  SCC splits. Cache lookup happens before otherwise-unused coverage/bounds work.
  Computed coverage, bounds and summaries are data, not negative proofs, and are
  not retained across rounds by this change. A negative is never an exhaustion
  record and cannot turn an unsupported region inconclusive. Metadata and
  invalidation work are charged, and cache state ends with admission. Complete
  runs must preserve proofs and diagnostics; saved work may improve limited runs,
  whose differences must be reviewed for soundness. Per-round measurements separate
  proof savings from rebuilt prerequisites before extending reuse further.
- **Index original dependencies within a checking invocation.** Repeated full
  scans made local query construction depend on the size of unrelated fixed
  evidence and on the depth of dependencies restored by rewrite proofs. A borrowed
  head index and worklist recover exactly the same originals, dropped alternatives
  and certificate dependencies, projecting each reached item once per query.
  Keep the index local to the invocation and release it after the local queries:
  retaining another keyed copy of the entire graph would reverse the memory savings
  from on-demand keys. This changes neither cache inputs nor logical receipts;
  the graph-sized index is physical metadata, not BDD storage or a session cache.
- **Assumption cones may be stratified after grounding.** Generic library relations
  can contain a relation-level negative cycle whose ends are used by different
  tuples. Requiring relation stratification forced authors to split those relations
  even when no ground cycle existed. The IR now classifies such cones for deferred
  validation; the checker follows independent dependencies from the assumption's
  ground atoms. Selected assumptions cannot prune this graph,
  and no admission proofs are used, so W's meaning never depends on W. Negative
  cycles elsewhere in the program do not invalidate an independent assumption.
  Validation is reported at program level; its selection policy is described below.
  Selecting an invalid or inconclusive assumption prevents that verification from
  running. Ground validation is fresh and bounded. This deliberately leaves
  assumption-free redundancy proofs for later. Fixed-truth specialization is now
  permitted as described below.
- **Fixed facts are evaluated once per run.**
  Large authored structures should not become repeated symbolic work in every
  verification. Relations reaching no inputs through either polarity can be
  evaluated independently of the selected context. Only settled atoms are folded;
  unresolved components keep existing admission and findings. Original fixed rules,
  dependencies, completed absences and presence derivations remain shared evidence,
  with their size reported separately from residual execution. This first version
  retains the full fixed graph rather than compacting away diagnostic information.
  The initial version left assumption validity unchanged. The subsequent
  fixed-truth specialization below deliberately broadens accepted cones.
  The fold has its own bounded allowance and receipt; retained atoms, rules and dependencies also count against
  preparation's size limits. Reuse is measured with the `.den` scorecard and the
  multi-verification benchmark.
- **Assumption validation and W share a fixed-truth specialization.** Grounding the
  entire original program for validation duplicated millions of fixed atoms already
  evaluated by the fold. Reusing the residual graph alone was insufficient: it keeps
  dead instances for evidence, so a false guard still connects a syntactic cycle.
  Validation now performs one specialization using exact assumption-independent
  fixed truth. False positive or true negative premises kill an instance; satisfied
  fixed premises disappear. Blocked atoms are never interpreted as false, and no
  newly exposed truth triggers another fold. This is sound independently of W:
  removing an impossible producer and substituting known constants preserves the
  rules' meaning in every input world. Assumptions cannot justify themselves or
  one another. A genuinely residual negative cycle still invalidates its cone.
  W is evaluated on that same view, avoiding a later failure on the unsimplified
  graph. Original instances and evidence remain intact for ordinary admission and
  rewrite warnings; specialization itself is not a rewrite finding.
  The sealed artifact retains the fold, original residual graph and specialized
  view, with one keyed cycle per root. Requests reuse the residual rather than
  grounding it again. Classification retains its relation-stratified fast path;
  unnamed restrictions use the same validity policy. Explicit all-declaration
  validation also works without verifications. The fold and residual-validation query have separate bounded allowances
  and receipts; the latter depends on the former. Logical exhaustion is explicit,
  established validity survives, and operational interruption installs no partial
  reusable artifact. Sharing is bound to snapshot, domains, keys and deterministic
  limits, and never caches validation across edits. Direct or relation-cache requests
  needing ground validation also use this preparation; requests with only
  relation-stratified restrictions keep their existing path.
- **Ground-validate only assumptions selected by the run.** Whole-program declaration
  validation spent substantial time grounding unused library assumptions, even for
  a partial CLI run. Resolve executed verifications first, then validate the union
  of their assumption keys once. Relation-stratified classification stays universal;
  unselected ground cones get Information with state `not-selected`, not an invalid
  or inconclusive result. They do not affect verdicts or exit codes. Selection uses
  declaration identity rather than relation identity, so aliases are not accidentally
  selected. No selected assumption supplies truth to validation; this is a scheduling
  change, not layered assumptions. When a selected cone needs it, the existing shared
  residual preparation and cycle index remain whole-program. Run selection and
  validation are fresh across edits, with the independent fixed fold still reusable.
  The explicit all-declaration API and `check-den --validate-all-assumptions` preserve
  the authoring check on demand, including without verifications.
- **Share a context, not its selected checks.** Residual grounding, permitted worlds,
  indexes and admission depend on the program, resolved domains, restrictions and
  deterministic limits. Obligation groups, notices, verification identity and
  example policy are separate attachments. Requests sharing a context still check
  their own selections; neither exhaustion nor an attachment can contaminate another.
  Context graphs remain bound to one source snapshot. Across snapshots, the single
  Salsa fold query retains semantic keys and original instance substitutions, then
  binds current evidence. The first query covers the whole fixed cone, preserving
  its whole-operation allowance. The existing possibility-grounding SCCs follow
  positive edges and cannot directly cache fixed truth through negative providers;
  finer fixed SCC invalidation is deferred pending measurements. No failed fold or
  incomplete cycle-relevant admission is reused as a completed artifact. Completed
  cycle admission may retain explicitly marked logical downstream exhaustion.
- **Keep a completed fixed fold without a separate byte cap.** There is one
  replaceable fold per program session, and checker limits already bound its work
  and atom/rule counts. The old quarter-of-session cap discarded larger completed
  folds while still paying for their portable form on every run. Retain that work,
  count its bytes separately, and leave the other cache pools' budgets intact.
  This accepts additional retained memory; the count is conservative payload
  accounting, not a measured peak or RSS limit. Reset, eviction and failed or
  interrupted fold preparation release it. Setting `max_entries` to zero explicitly
  disables retention and uses direct preparation, avoiding reconstruction/export;
  semantic outcomes agree, while chosen evidence and transfer receipts may differ.
- **Cycle diagnostics show retained ground dependencies.** A generic rule can have
  many instances with different recursive behavior. Showing concrete arguments and
  signed edges identifies the reported instance without searching for a new cycle
  or changing checking work. The displayed path is structural evidence; no-meaning
  retains its separate input observation, and the path is not a minimal inconsistent
  subset or an execution trace. Frontends share this rendering and keyed evidence;
  DSLs can keep their own vocabulary. Finding identities and verdicts are unchanged.
- **Conclusive answers must be sound.** A false counterexample or a silent success
  misleads the author; an explicit inconclusive or unsupported outcome does not. Hence
  counterexamples only after concrete replay (or certification); blocked or unknown
  facts are never evidence of absence.
- **Certification search preserves whole-program certification.** Emptiness and
  coverage may exclude equivalent input worlds using the target cones plus every
  blocked component's cone. Using only the target would miss cases where an unrelated
  component decides certification; certifying just the target would change existing
  results. Complete dependency discovery is required, selected assumptions still
  constrain witnesses, and an unresolved outcome stays unresolved. This removes
  repeated attempts across irrelevant inputs without changing admission or limits
  ([policy](checker-policies.md#certification-search)).
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
- **Library rewrite noise is an optional view filter.** A rewrite proof may hold in
  one consumer and fail in another, so a per-library merged warning would lose its
  verification context. Keep all proofs and finding identities. The CLI's
  `--hide-library-rewrites` and editor's `denotate.showLibraryRewrites: false` hide
  only diagnostics for rewritten rules owned by included libraries. Use rule
  ownership, not primary location or namespace; retain unknown ownership. Keep
  home-program warnings, other diagnostics, full status inventories and exit codes.
  Report the hidden finding count so a filtered view does not imply a clean check.
- **Several emptiness examples belong to one finding.** Independent invalid tuples
  should be visible together, without changing the obligation/verification identity
  when an author fixes one. By default retain up to three confirmed tuples in semantic-key
  order, each with its own world, replay scope and bounded attribution. Count
  distinct tuples across worlds, exactly when checking completes and as a lower
  bound otherwise. Keep the semantic scan order and its existing work charges;
  sample retention does not spend the semantic allowance. Attribute each retained
  tuple after checking with a fresh allowance, then union its locations and label
  them with the tuple. Per-tuple identities are deferred until suppressions, waivers
  or another consumer needs to track individual errors; introducing them now would
  add identity and publication machinery without a consumer.
- **Emptiness sampling is an invocation-level reporting choice.** Debugging a
  generated library sometimes requires seeing every invalid tuple: an omitted
  example must not be mistaken for an impossible one. `check-den --empty-examples
  N|all` and `PreparedCheck::with_emptiness_examples` control retention, with the
  editor's default unchanged. Keep this outside the semantic request and cache
  inputs; sessions already recompute emptiness evidence. Scan and deterministic
  charges stay unchanged; retain all by appending during the scan and sorting once
  afterwards. Additional worlds and attribution consume memory and time. `all`
  means all confirmed tuples, not all worlds or derivations, and a count remains a
  lower bound when checking is incomplete. No per-tuple identity is needed.
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
  unsupported or incomplete meaning stays unknown, with one Information diagnostic
  at the notice declaration. This distinguishes unanalysed conditions from quiet,
  varying ones without changing verdicts or exit codes. The checker retains keyed
  blockers and cycle rules or the phase/resource cause; presentation does not infer
  dependencies again. Inconsistent assumptions keep only the existing context Error
  and never produce notices by vacuity. The author supplies the complete enclosing scope;
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
