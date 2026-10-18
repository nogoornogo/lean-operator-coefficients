# Specified VEV Stabilizer

- ID: `vev-stabilizer`
- Status: completed
- Result type: algebraic proof package
- Working branch: `proof/vev-stabilizer`
- Integration target: `master`; merge authorized at stage 01. No push authorized.

## Frozen First Endpoint

Classify the exact stabilizer, not merely a subgroup of fixing elements, of a
specified two-eigenvalue adjoint VEV. First prove an arbitrary-size matrix
criterion over a field, then specialize to SU(5) and
`diag(2,2,2,-3,-3)` in the existing color-first coordinates.
The action is conjugation, and fixing the VEV means equality of the vector,
not preservation of its line. Distinct eigenvalues are essential; eigenvalue
collision must give the entire group as a regression control.
The SU(5) carrier is the complex traceless-matrix adjoint convention; the
displayed Hermitian VEV is not asserted to be an anti-Hermitian Lie-algebra
element in a different convention.

The output is necessary and sufficient block-diagonal membership with unitary
blocks and product determinant one: the exact embedded S(U(3) x U(2)), not an
incorrect injective SU(3) x SU(2) x U(1) covering product. Use the existing SM
covering embedding to prove inclusion. Surjectivity/kernel of that cover and
operator-Hom connections are subsequent scoped milestones, not assumed here.

## Plan

Authorized continuation: prove an explicit block-pair group equivalence, equality
of the SM covering image with this stabilizer, its existing central cyclic
order-six kernel, and the quotient/stabilizer group equivalence. Transport
arbitrary algebraic intertwining Hom spaces along the surjective cover; descent
of a covering-group representation requires the explicit trivial-kernel-action
condition. No finite-dimensional or continuity hypothesis is added to Hom
transport. The unbroken gauge stabilizer does not automatically identify an
independently supplied residual flavor group. Stop before any new physical
scope or general vacuum classification.

1. Prove general diagonal commutation and two-eigenvalue block criteria.
2. Construct the SU stabilizer subgroup and explicit block characterization;
   prove conjugation fixing is equivalent to commutation.
3. Apply to the specified SU(5) VEV, verify tracelessness and the existing SM
   embedding inclusion. Include a color/weak mixing element that does not fix it.
4. Audit strict transitive axioms, focused/full builds, layout and links; commit
   coherent milestones. Then assess the exact covering-group and residual-Hom
   bridge without replacing independently supplied model inputs by assumptions.

No Higgs-potential minimization, arbitrary vacuum search, topological charge,
RGE, mass/rate prediction or literature premise is part of this endpoint.
Preserve toolchain pins and all existing theorem hypotheses.

## Existing Assets And Distinctions

- [Standard-vector stabilizer](../../../Math/LieGroups/SpecialUnitary/VectorStabilizer.lean)
  already identifies SU(n) inside SU(n+1); it is not a new result of this topic.
- [SU(5) covering embedding](../../../GUT/SU5/Embeddings/StandardModel.lean)
  has exact color/weak blocks and determinant normalization.
- [SU(6) vacuum-fixing elements](../../../GUT/SU6/Yukawa/VacuumStabilizer.lean)
  provide invariance and bounds, not an exact full-stabilizer classification.
- [Common operator completeness](../operator-completeness-interface/README.md)
  was merged as `checkpoint 01`; its residual group remains an input. Li's entire
  basis algorithm was not formalized. This topic complements the input side.

## Verification

At branch creation, merged `lake build` passed (6040 jobs); this is the common
completeness baseline, not yet verification of new stabilizer sources.
The documentation-only closure update passed links/diff checks without a new
Lean build before merge; the merged build was then rerun successfully.
Unrelated user documentation changes remain uncommitted and excluded.

Group/Hom continuation verification (stage 01):

- `lake build GUT.SU5.Audit.AuditAdjointVEVStabilizer`: passed, 3520 jobs,
  42 strict transitive checks with the same three allowed foundational axioms.
- Full `lake build`: passed, 6048 jobs. New sources have no warnings;
  pre-existing dependency warnings replayed. Intermediate elaboration errors
  and a style warning were corrected before these final accepted checks.
- Layout: passed, 995 modules. Local links: passed, 352 documents, 2235 links,
  34 heading fragments, zero errors. `git diff --check` passed.
- No pins, custom axioms, audit exceptions or resource limits changed.
  No unrelated operator computational tests were rerun, as their definitions
  and normalization conventions are unchanged.

First milestone verification (stage 01):

- `lake build GUT.SU5.Audit.AuditAdjointVEVStabilizer`: passed, 3179 jobs,
  17 strict transitive checks; only propext, Classical.choice and Quot.sound.
- Full `lake build`: passed, 6044 jobs. No new-source warnings; pre-existing
  dependency warnings replayed. Local elaboration failures were corrected
  before these accepted builds; no failed audit is treated as verification.
- `node tools/layout/check-layout.mjs`: passed, 991 modules.
- `node tools/docs/check-links.mjs`: passed, 351 documents, 2226 local links,
  34 heading fragments. `git diff --check` passed.
- Pins and axiom allowlists unchanged. No external calculation is a premise.
  Existing operator normalization scripts were not rerun for this milestone,
  since their definitions and tests are unchanged by the new sources.

## First Milestone

- [Diagonal centralizer](../../../Math/LinearAlgebra/DiagonalCentralizer.lean):
  arbitrary finite index sets over a field; distinct eigenvalues force precisely
  the mixed entries to vanish. Eigenvalue collision removes this restriction.
- [SU adjoint stabilizer](../../../Math/LieGroups/SpecialUnitary/AdjointStabilizer.lean):
  conjugation fixing iff commutation, an actual subgroup, and necessary and
  sufficient unitary-block/product-determinant characterization.
- [SU(5) application](../../../GUT/SU5/Symmetry/AdjointVEVStabilizer.lean):
  the unchanged color-first embedding fixes the explicit traceless VEV.
  `classification` and `mem_iff_cross_entries` characterize the entire stabilizer,
  not just those elements that happen to belong to the SM covering image.
- [Strict audit](../../../GUT/SU5/Audit/AuditAdjointVEVStabilizer.lean):
  17 transitive axiom checks, including zero/collision and a color/weak mixing
  element that fails to fix the VEV. Its determinant is computed over rationals
  by `decide +kernel` and transported to complex numbers; no external oracle,
  `native_decide` or resource-limit increase is used.

The first matrix-membership endpoint and the authorized group/Hom continuation
are proved. See [global group and Hom results](global-group.md) for the explicit
block equivalence, surjective SM cover, central order-six kernel, faithful
quotient and necessary-and-sufficient representation descent condition.
General VEV classification and identification of an additional flavor group
remain outside scope. Master merge: `checkpoint 02` (stage 01), including the
completed flavor-stabilizer child. Topic branches are retained.

The bounded [specified flavor-stabilizer child](../flavor-stabilizer/README.md)
constructs symmetry from additional supplied coupling/VEV data. It does not
infer that extra data or a flavor group from the SU(5) adjoint VEV alone.

Subsequent independent topics prove the
[full diagonal Majorana stabilizer](../majorana-unitary-stabilizer/results.md)
and [Takagi existence with arbitrary-basis stabilizer/Hom transport](../majorana-congruence-interface/existence.md).
The latter covers all finite complex symmetric matrices, not simultaneous
Yukawa classification or a flavor group inferred from the adjoint VEV.
