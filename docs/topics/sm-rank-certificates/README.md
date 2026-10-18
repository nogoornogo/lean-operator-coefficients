# Exact rank certificates and content compression

- Status: constant L/conjugate-L and Q/conjugate-Q local support and symbolic
  nullities verified; binary mixed-source decomposition and character product
  verified; arbitrary-content mixed-chirality compact comparison and
  ten-species source decomposition/dimensions verified;
  conditional mixed-content local extraction and existing scalar q/l support
  iff verified; numerical evaluation and other residual classes remain open
- Branch: `proof/sm-rank-certificates`
- Integration target: `proof/llhh-kernel-rank`
- Parent exception: bounded child of the unmerged LLHH branch.
- Authorization: user requested a formalization attempt extending the LLHH
  result toward general exact matrices and all-content ranks.

Master integration was authorized at stage 01 and includes this topic at
`checkpoint 01`; the original branch/parent target above remains historical. See
[merged-state verification](../sm-rank-certificates/verification.md#master-integration-at-stage-01).
No remote push was authorized or performed.

The later [readability review](../proof-readability-review/rank-replacement.md)
replaces the small generated example certificates with arbitrary-vector
reconstruction. The general rank and field-transport statements are unchanged.

## Frozen plan

1. Develop a reusable rank certificate over exact fields. A factorization
   `A=B*C`, with a left inverse for B and a right inverse for C, should certify
   the inner dimension as rank. Transport rational certificates to complex
   matrices using a field homomorphism. Prove and test a nontrivial example.
2. Prove that species words with identical multiplicities give the same
   statistical source and the same local kernel rank. This removes order
   redundancy from the all-content problem without guessing an invariant basis.
3. Assess whether these connections provide an executable exact matrix for
   every content. Continue within these interfaces; if the remaining need is
   a new all-content weight-multiplicity or coordinate-field bridge, record
   that prerequisite explicitly. Do not claim all ranks evaluated from a
   conditional certificate or a compression theorem alone.
4. Focused builds, persistent transitive axiom audits, full build, layout,
   links, diff review and verified commit.

Arbitrary abstract complex entries are not a decidable exact input format.
The computational boundary is rational/explicit-field data plus checked
identities. No numerical zero tolerances, extra axioms, dependency changes,
or brute-force materialization of the full table. No master merge or push.

## Numerical continuation

The user requested numerical classification using the current connections.
First certify closed dimension/rank formulas for every constant-species
content: `choose(species dimension,n)*(m+1)` columns, rank zero above species
capacity, and full numerical rank when hypercharge is incompatible. Generate
an exact partial table over the finite Higgs-reduction indices for all such
contents within species capacity, include the proved LLHH neutral result,
and explicitly distinguish all unresolved neutral entries. This is a subset
of the all-content objective, not a replacement or completed classification.
Do not enumerate the trillion-size mixed-content box. The uniform mixed-content
source/carrier dimension bridge is now proved in the iteration result below;
invariant-multiplicity extraction remains open. Verification and commits as above.

## Guidance and sources

- [Computable character successor](../sm-computable-characters/results.md):
  actual six-coordinate slot weights, executable reference terms and conditional
  kernel/support consumers; all-107 evaluation remains deferred at the
  binomial-size reference boundary.

- [Fixed-input q/l pattern facade](pattern-input-results.md) and
  [plan](pattern-input-plan.md): existing forbid/allow requests become finite
  actual support tests with a proved bridge to original all-degree spaces.

- [Existing q/l support extraction](ql-extraction-results.md) and
  [consumer plan](ql-extraction-plan.md): residual charge neutrality composed
  with local multiplicity positivity, eliminating `Allowed(T)` for the
  original all-degree q/l coefficient space under the Weyl input.


- [Actual compact extraction](compact-extraction-results.md): constructs
  combined compact coefficients, joint continuity and the finite integer
  inverse-character presentation for every content. Only the Weyl reduction
  law remains external in the local multiplicity/support/rank statements;
  the spectral construction is noncomputable; the q/l consumer is linked above.


- [Conditional Weyl extraction](weyl-input-results.md) and
  [authorized plan](weyl-input-plan.md): established Weyl reduction as an
  explicit theorem parameter; finite A2 extraction and conditional actual
  kernel/support/rank consequences. The subsequent actual compact extraction
  result constructs the comparison, continuity and torus presentation.


- [Finite-tree exterior iteration](iterated-mixed-results.md): arbitrary
  disjoint-family induction and actual-source decomposition, product dimensions/
  characters and supported coefficients; the ten-species dictionary and
  arbitrary ordered SM content dimension/carrier connections are now proved.

- [Mixed-chirality compact comparison](mixed-chirality-results.md): actual
  paired/independent compact coefficient equivalence at arbitrary content,
  gauge/residual retention, original Higgs support and finite-kernel transport.

- [Mixed mathlib continuation](mixed-mathlib-plan.md) and
  [binary mixed-source result](mixed-mathlib-results.md): full-action exterior
  decomposition, supported coefficient transport, character products and SM
  two-species dimension/rank connections.

- [External-library assessment](external-library-assessment.md): pinned ATLAS,
  LeanPool and Physlib candidates; an already available mathlib product-exterior
  equivalence and the remaining A2 proof boundary. No dependency change.

- [Q/conjugate-Q exact coordinate result](q-gaussian-results.md):
  actual Gaussian-rational constraints, uniform polynomial nullities,
  local support and original matrix rank; Route B completion boundary.

- [Uniform L/conjugate-L multiplicities](lepton-multiplicity-results.md):
  finite symbolic weight formula, actual local coefficient/kernel dimensions,
  complete local support criteria; Q is now covered by the Route B result.
- [Structural character milestone](structural-character-results.md):
  degree-uniform exterior/actual-L character formulas and A1 extraction;
  SL2 Clebsch–Gordan and compact invariant preservation for two symmetric
  powers, arbitrary iterated tensors/exterior quotients, and the actual L/Higgs
  compact Weyl coefficient-space comparison. Compact coefficients now connect
  to the actual finite kernel; the L/conjugate-L multiplicity adapter is now
  proved in the linked result.
- [Neutral-row literature assessment and proposed plan](neutral-literature-plan.md):
  the 107 constant-content rows do not require a general mixed-content bridge;
  target a degree-uniform structural multiplicity/support theorem. Fixed-degree
  L proofs are provisional milestones; numerical enumeration is not completion.
- [Results and precise remaining bridge](results.md)
- [Numerical continuation](constant-results.md): certified constant-content
  partial table and all-content odd-degree full-rank theorem.
- [Verification](verification.md)
- [LLHH rank result](../llhh-kernel-rank/results.md)
- [Literature and application boundaries](../llhh-kernel-rank/literature.md):
  Milne's base-change result motivates exact coefficient models; invariant
  counting references motivate content compression. No literature premise.
- [Source](../../../Math/RepresentationTheory/PatternExteriorSource.lean)
- [Support](../../../Math/RepresentationTheory/PatternCoefficientSupport.lean)
- [Actual kernel](../../../Physics/StandardModel/Operators/SMFullLocalKernel.lean)
- Pinned mathlib `LinearAlgebra/Matrix/Rank.lean`: matrix rank inequalities
  and rank of the identity supply the certificate proof.
