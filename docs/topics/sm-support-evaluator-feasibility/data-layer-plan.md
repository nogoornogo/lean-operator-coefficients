# Executable support data with ordinary semantic proofs

The [implementation record](data-layer-results.md) reports a verified partial
result and the resource stop. The [subsequent revision](data-connection-results.md)
verifies the SM bridge and ordinary consumers; the original contract below is retained.

## Authorization and endpoint

The user authorized (1) executable data definitions and (2) proofs connecting
those definitions to existing support conditions. Individual support judgments
must use ordinary lemmas and explicit witnesses; computational proofs are not
permitted. This is a plan, not a claim that the new layer already exists.

Continue the bounded extension on `audit/sm-support-evaluator-feasibility`,
from verified checkpoint `checkpoint 01`; the recorded integration target remains
`master`. No merge, push or broad solver rewrite is authorized. Preserve the
original topic base and earlier phase evidence.

Deliver a uniformly defined executable data layer for all ten signed species,
all single-generation exterior degrees (including overflow), three-generation
occupations, content composition and Higgs weak labels. Prove its support
predicate equivalent to `SMJointContentSupport.Supports`, and derive the
corresponding Higgs/original-space interface using existing theorems.
Do not replace `SMJointHiggsSupport.original_ql_iff` or the actual statistical
coefficient spaces. Fixed SM/Higgs and scalar cyclic q/l conventions stay fixed.

## Proof policy

- Use structural induction, explicit case splits, constructors, witnesses,
  existing representation/decomposition lemmas, rewriting and simplification.
- Do not use `decide`, `decide +kernel`, `native_decide`, `by decide`, Boolean
  reflection to discharge support judgments, or generated exhaustive proofs
  of closed instances. Do not use `omega`/`norm_num` to solve new closed
  judgment or correspondence goals. Use general arithmetic lemmas instead.
- Ordinary definitional equality (`rfl`), rewriting and constructor reduction
  remain available. They are part of ordinary Lean proofs, not a separate
  support decision procedure. No custom axiom, `sorry`, proof-limit change,
  dependency change or audit exception.
- Existing computationally proved results remain historical verified evidence;
  this work does not reprove the 107 signs or 572 assignments. New semantic
  bridges must not depend on those certificate files or their result tables.
- Compilation and, if useful, `#eval` of data summaries are diagnostics only.
  Their outputs are never imported as theorem premises or used to close goals.
  Acceptance of correspondence comes from ordinary kernel-checked proofs.

## Interfaces and ownership

Prefer the existing purely syntactic `JointSourceExpression.Expr`,
`JointColorSpinWord.Atom`/`Word`, and `RestrictedColorWordSupport.Kind` where
these can be used without noncomputable data projections. Their enclosing
`noncomputable section` alone is not evidence that every declaration needs
replacement. Inspect actual generated-code dependencies before adding types.

The following are proposed interfaces, with names finalized during source
inspection rather than treated as existing declarations:

1. `coreData s n : Expr`: construct zero/atom/sum/tensor syntax directly from
   degree cases and numerical color/weak/left/right labels. Its runtime path
   must not project an expression from `Presentation` or a representation
   equivalence. Prove uniformly
   `coreData s n = (SMSignedCoreJointPresentation.presentation s n).expression`,
   or a proved support-preserving equivalence if syntactic equality fails for
   an identified reason. Any such change must preserve joint branch choices.
2. `expressionData c m o : Expr`: compose core data using explicit numerical
   occupation indices and tensor operations, then add the weak Higgs atom.
   Reuse `CompactGenerationOccupations.equiv` for the correspondence with
   existing occupation choices; no range-of-generation-words enumeration.
   Prove the expression correspondence after that explicit reindexing.
3. `DataSupport c m : Prop`: existential joint support over the data-layer
   occupations and branches. Prove `DataSupport c m ↔
   SMJointContentSupport.Supports c m` in both directions, with constructive
   transport of a witness. Keep color, weak and both spins on the same branch.
4. Derive Higgs support equivalence and an original-space corollary retaining
   the original residual and hypercharge equations, using `original_ql_iff`.
   No new Weyl, numerical-rank or supplied-occurrence hypothesis is permitted.

Reusable syntax/composition and their structural proofs belong under `Math/`;
the SM species dispatch and model bridge belong under `Physics/`. Likely files
are `Math/RepresentationTheory/JointSourceData.lean` (only if genuinely needed)
and `Physics/StandardModel/Operators/SMJointSupportData.lean`, with separate
bridge/audit modules if dependencies warrant them. Data definitions must remain
compilable independently of their noncomputable semantic interpretation.
Register actual new modules in their layer aggregates and retain import gates.

## Implementation stages and gates

1. **Dependency inspection and one complete core family.** Trace expression
   projections in the lepton/single-spin presentations. Implement a uniform
   lepton or electron data function, including vacuum and overflow, and prove
   its correspondence by ordinary degree cases. Compile that function with a
   runtime degree argument. Do not substitute closed elaborator-normalized
   expressions for a uniform function. Stop if a new representation theorem
   rather than metadata extraction is needed.
2. **All signed cores.** Extend through colored singlet-weak cores and Q,
   then their conjugates/duals, reusing the existing decompositions. Prove
   ordinary symbolic correspondences for every degree, not a table of closed
   `rfl`/decision checks. Preserve source-owner information for color flags.
3. **Composition and semantic bridge.** Prove tensor/sum and generation
   composition by induction; reindex occupations through the existing compact
   equivalence. Establish both support directions and the Higgs/original-space
   corollaries. No global replacement of old decision instances.
4. **Ordinary proof consumers and compilation.** Add a small fixed set of
   consumers: vacuum/overflow, a nontrivial mixed positive witness and a
   negative structural filter. Construct them with explicit occupations,
   components, coupling paths/diagrams and ordinary lemmas. For negatives,
   use an existing general exclusion theorem or a structural impossibility
   proof; never infer prohibition from failed search. Demonstrate executable
   metadata construction for a parameterized signed-core/content input.

Each stage is a verified checkpoint; continue through these gates unless an
explicit stop condition below applies. This plan does not claim that compilation
of data also makes the existing general `Decidable` functions executable.

## Verification, resource policy and stop conditions

Run focused builds, persistent strict transitive axiom audits for new bridges
and consumers, then one serialized full build. Inspect new proof dependencies
for compliance with the no-computational-proof policy, beyond the axiom audit:
an axiom audit alone cannot enforce that policy. Run layout, local-link and
diff checks. Keep pins/options unchanged; one Lean run at a time, 300 seconds
per guarded run, sampled RSS at most 10 GiB with 4 GiB host reserve. Record
successful under-limit time/peak as well as interrupted/failed runs; report
sampling overshoot. Keep disposable logs outside source control.

Stop and record the precise missing interface if the proposed correspondence
needs a new foundational classification, cannot preserve joint witnesses,
requires computational proofs or fails the existing resource guard. Do not
quietly replace the theorem by an extra assumption or try an unapproved new
algorithm. A metadata-layer endpoint is independent of search scalability.
Reachable-spin DP, new color matching/pruning, a general compiled Boolean
solver, new exhaustive tables, and rewriting earlier certificates are outside
this implementation. Revisit those only through a separately frozen scope.

Update this topic's results, the proof dossier and assumptions ledger when
new library results are verified; commit coherent checked milestones. The
present planning-only change requires links/diff checks, not a new Lean build.

## Planning checkpoint verification

Documentation-only: local links passed (975 Markdown files, 5941 local links,
112 fragments, zero errors), with the existing read-only checker's sandbox
subprocess retry; `git diff --check` passed. No Lean build or axiom audit was
rerun, and no new proof baseline is claimed. Implementation has not started.
