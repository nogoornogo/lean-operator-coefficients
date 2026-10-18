# Initial Source Register

These inspected local assets are starting points, not proofs of the new targets.
Library support can supply algebraic primitives; it does not replace the
model-specific semantic, support or completeness certificates.

| Source | Role and limit |
|---|---|
| [Previous outcome](../prohibition-converse-boundaries/results.md) | Frozen distinction between selected iff, mass existence, counterexamples and unclassified support |
| [DipoleFlavorSelection](../../../Physics/StandardModel/Operators/DipoleFlavorSelection.lean) | Actual B/W allowance iff nonzero intertwiner evaluation; common constituents classify total coefficients only |
| [CyclicSelectorDipoleSelection](../../../Physics/StandardModel/Operators/CyclicSelectorDipoleSelection.lean) | Arbitrary diagonal cyclic selectors, comparison control |
| [FiniteSemisimpleDecomposition](../../../Math/RepresentationTheory/Decomposition/FiniteSemisimpleDecomposition.lean) | Finite abstract decomposition exists; does not automatically compute common irreducible labels |
| [Schur](../../../Math/RepresentationTheory/Decomposition/Schur.lean) | Endomorphisms of finite-dimensional complex irreducibles are scalar |
| [CommonIrreducible](../../../Math/RepresentationTheory/Decomposition/CommonIrreducible.lean) | Nonzero Hom criterion; selected evaluation needs additional information |
| [InverseCyclicSMCharges](../../../Physics/StandardModel/Operators/InverseCyclicSMCharges.lean) | Actual neutral DUQL coordinate and bounded three-generation iff |
| [DeltaLOneSignedFields](../../../Physics/StandardModel/Operators/DeltaLOneSignedFields.lean) | Actual signed gauge/Weyl/flavor fields and conventions |
| [BnvMixedInput](../../../Physics/StandardModel/Operators/BnvMixedInput.lean) | Actual mixed coefficients, parity, bounded degree gates; no global scalar-degree cutoff |
| [AdmittedCyclicSMProhibition](../../../Physics/StandardModel/Operators/AdmittedCyclicSMProhibition.lean) | Support-guarded all-degree charge iff and neutral odd-degree control |
| [InverseLeptonParitySelection](../../../Physics/StandardModel/Operators/InverseLeptonParitySelection.lean) | Existing all-degree positive control |
| [SymmetricPowerDescent](../../../Math/RepresentationTheory/SymmetricPowerDescent.lean) | Existing symmetric-power descent input; dressing multiplication still needs a certificate |

Under unchanged pins, mathlib contains symmetric/exterior algebra and finite
permutation-group primitives, and the repository imports TauCeti exterior and
symmetric powers. None of this is claimed to prove a finite SM covariant seed
list. Record exact reused declarations when the implementation route is selected.

No external paper, Hilbert series or generated operator list is a premise.
Any later literature search must preserve a source/version/location record,
its candidate-versus-assumption role and the proof connecting it to the domain.

## Implemented sources

- [FiniteBlockHom](../../../Math/RepresentationTheory/Decomposition/FiniteBlockHom.lean):
  actual product-action intertwiners and rectangular block-Hom equivalence.
- [IrreducibleHomScalar](../../../Math/RepresentationTheory/Decomposition/IrreducibleHomScalar.lean):
  matching bridge scalar equivalence and unmatched-zero proof using Schur.
- [IrreducibleBlockCoordinates](../../../Math/RepresentationTheory/Decomposition/IrreducibleBlockCoordinates.lean):
  full matching-pair coordinate equivalence and proved matrix-unit expansion.
- [ScalarIrreducible](../../../Math/RepresentationTheory/Decomposition/ScalarIrreducible.lean):
  scalar flavor representations are irreducible.
- [ExternalUnitEquivalence](../../../Math/RepresentationTheory/ExternalUnitEquivalence.lean):
  actual neutral one-copy external fields and their tensor-unit equivalence.
- [InvariantQuadraticPowers](../../../Math/RepresentationTheory/InvariantQuadraticPowers.lean):
  r-fold paired multilinear map, symmetrization, symmetric quotient descent,
  invariance and nonzero pure-tensor evaluation.
- [MixedInvariantDressing](../../../Math/RepresentationTheory/MixedInvariantDressing.lean):
  actual tensor-product coefficients, linearity and nonzero evaluation product.
- [S3DipoleSelection](../../../Physics/StandardModel/Operators/S3DipoleSelection.lean):
  concrete nonabelian action, centralizer, exact selector iff and control.
- [SemisimpleDipoleSelection](../../../Physics/StandardModel/Operators/SemisimpleDipoleSelection.lean):
  actual decomposition transport and matrix-unit selector iff.
- [CyclicSemisimpleDipoleControl](../../../Physics/StandardModel/Operators/CyclicSemisimpleDipoleControl.lean):
  concrete certified cyclic decomposition consumer.
- [NeutralHiggsPowers](../../../Physics/StandardModel/Operators/NeutralHiggsPowers.lean):
  actual Higgs/dual action, invariant pairing, normalization and all-power functionals.
- [DressedDuqlFamily](../../../Physics/StandardModel/Operators/DressedDuqlFamily.lean):
  actual DUQL-only reconstruction, dressed coefficient range and all-power charge iff.
- [ThreeGenerationFermionBound](../../../Physics/StandardModel/Operators/ThreeGenerationFermionBound.lean):
  actual species dimensions, degree-180 exterior vanishing and finite count superset.

Reused library declarations include the unchanged mathlib finite permutations,
Schur theorem over algebraically closed C, multilinear composition and finite
sums, and TauCeti SymmetricPower.lift and exteriorPower.eq_zero_of_finrank_lt.
The library power primitives are not attributed a full SM support theorem.
The actual mass-pair pullback reuses local LightInheritanceBoundary and
EquivariantWeylMassTransport. No new external paper is a proof premise.

## Inspected support-reduction boundary

- [FourWeakWeylCompleteness](../../../Physics/StandardModel/Operators/FourWeakWeylCompleteness.lean):
  four-doublet invariant coordinates, not uniform arbitrary-degree covariant generation.
- [SymmetricPowerLowDegree](../../../Math/LinearAlgebra/SymmetricPowerLowDegree.lean):
  zero/one degree equivalences, not a global scalar cutoff.
- [SpechtIsotypicLabels](../../../Math/RepresentationTheory/SpechtIsotypicLabels.lean):
  labels for supplied symmetric-group isotypic components, not actual SM gauge support.

The [boundary record](support-boundary.md) identifies the missing complete
covariant interface. Search absence is limited to inspected local assets,
not asserted absence of literature or of possible mathematical proof routes.

## Covariant literature assessed at stage 03

| Source and inspected location | Role and limit |
|---|---|
| [Grinstein, Lu, Merlo and Quilez, arXiv:2312.13349v1](https://arxiv.org/html/2312.13349v1), 2023-12-20; sections 2.2.4 and 3.4 | Module structure, relations and explicit finite-generation citation to Theorem 3.24 of reference [7]. Underlying book theorem not independently inspected; no Lean premise introduced. |
| [Erickson and Hunziker, Stanley decompositions of modules of covariants](https://alco.centre-mersenne.org/articles/10.5802/alco.491/), Algebraic Combinatorics 9(2026), no. 3, 739-788, DOI 10.5802/alco.491; online 2026-07-01 | Journal abstract and publication record inspected. Constructive classical-group candidate; full proof and SM specialization not inspected or certified. |

The [assessment](covariant-literature-assessment.md) separates graded operator
support from fixed-VEV evaluation, and mathematical existence from a Lean
spanning certificate. These sources inform a possible continuation only.

## DUQL continuation sources

- [DuqlHiggsContent](../../../Physics/StandardModel/Operators/DuqlHiggsContent.lean):
  actual whole-content support definition, projection, hypercharge and cyclic
  necessity, dictionary-based witness and all-Higgs support iff.
- [FiniteSeedEvaluation](../../../Math/LinearAlgebra/FiniteSeedEvaluation.lean):
  evaluated span and linear zero tests given an explicit spanning certificate.
- TauCeti.RepresentationTheory.SU2.Weight, inspected under the unchanged pin:
  weightBasis, symPower_torusHom_weightBasis and eq_span_weightBasis_mem
  concern actual symmetric powers and torus-stable subspaces; they do not
  prove the required complete mixed covariant multiplication theorem.
- TauCeti.RepresentationTheory.SU2.Completeness, inspected under the unchanged
  pin: trace_mul_character_symPower is explicitly a character identity, not
  an actual Clebsch--Gordan representation equivalence.
- TauCeti.LinearAlgebra.SymmetricPower.Basis, inspected under the unchanged
  pin: monomial bases and rank formulas, not invariant covariant spanning.

No new literature theorem is a proof premise in this continuation.

## Four-family continuation sources

- [FourFamilyHiggsContent](../../../Physics/StandardModel/Operators/FourFamilyHiggsContent.lean):
  shared actual support/projection, charge and balanced dressing proofs,
  actual zero-Higgs coordinate transport and union-space iff.
- [DeltaLOneFamilyCompleteness](../../../Physics/StandardModel/Operators/DeltaLOneFamilyCompleteness.lean):
  actual duqlEquiv, qqueEquiv, qqqlEquiv and duueEquiv; statistics are already
  proved in these dictionaries and remain part of witness reconstruction.
- [FlavoredCyclicSelection](../../../Physics/StandardModel/Operators/FlavoredCyclicSelection.lean):
  four residual coordinate equivalences and their actual typed index spaces.
- [InverseCyclicSMCharges](../../../Physics/StandardModel/Operators/InverseCyclicSMCharges.lean):
  universal QQUE/QQQL charge lemmas for the statistics-aware coordinates.
- [TripleSymmetricCoordinates](../../../Math/RepresentationTheory/TripleSymmetricCoordinates.lean):
  QQQL's sorted symmetric triple index, used for an explicit coordinate witness.

No new external literature premise was introduced.

## Generic content adapter sources

- [ContentHiggsSupport](../../../Physics/StandardModel/Operators/ContentHiggsSupport.lean):
  actual arbitrary-degree support and seed spaces, constant-charge necessity,
  neutral-seed dressing iff and four-family consumers.
- [BnvMixedInput](../../../Physics/StandardModel/Operators/BnvMixedInput.lean):
  hypercharge_of_nonzero and actual pure-species value extensionality.
- [MixedWeightSupport](../../../Math/RepresentationTheory/MixedWeightSupport.lean):
  actual scalar-action obstruction on exterior/symmetric tensor carriers.
- [AdmittedCyclicSMProhibition](../../../Physics/StandardModel/Operators/AdmittedCyclicSMProhibition.lean):
  actual odd-degree coefficient vanishing.
- [ThreeGenerationFermionBound](../../../Physics/StandardModel/Operators/ThreeGenerationFermionBound.lean):
  above-180 actual coefficient vanishing.

All sources retain their existing conventions and pins. No new literature
result is supplied as a theorem premise.

## Outside-family trial sources

- [OutsideFamilyHiggsTrials](../../../Physics/StandardModel/Operators/OutsideFamilyHiggsTrials.lean):
  actual empty-degree seed, pure-scalar support iff, triple-Q parity control
  and actual six-quark charge/count necessity.
- [GradedSixQuarkComparison](../../../Physics/StandardModel/Operators/GradedSixQuarkComparison.lean):
  inspected two-species specified six-quark field/quotient correspondence;
  not an assumed dictionary into the ten-species signed carrier.
- [SixQuarkFlavorResidualHom](../../../Physics/StandardModel/Operators/SixQuarkFlavorResidualHom.lean):
  inspected invariant flavored Hom coordinates with explicit species alternation;
  no neutral raw tensor is promoted to a supported full-field seed.
- Unchanged mathlib exteriorPower.alternatingMapLinearEquiv and
  AlternatingMap.constOfIsEmpty supply the degree-zero actual seed construction.

No external literature theorem or separate six-quark nonzero claim is a
premise of the unconditional trial results.

## Actual six-quark connection sources

- [SixQuarkFullSeed](../../../Physics/StandardModel/Operators/SixQuarkFullSeed.lean):
  actual field projection/right inverse, cyclic/gauge/Lorentz pullback,
  supported nonzero seed and all-Higgs content iff.
- [SixQuarkTwoCoordinates](../../../Physics/StandardModel/Operators/SixQuarkTwoCoordinates.lean):
  twoCoordinateEquiv supplies the actual statistically admissible local seed.
- [SixSlotSpeciesDegree](../../../Math/RepresentationTheory/SixSlotSpeciesDegree.lean):
  source degree-(2,4) exterior coefficient sector, already included in the
  physical six-quark dictionary; not assumed from a contraction list.
- [FiniteSpeciesExterior](../../../Math/RepresentationTheory/FiniteSpeciesExterior.lean):
  actual pure-species restriction and permutation_of_counts.
- [ExteriorWeightSupport](../../../Math/RepresentationTheory/ExteriorWeightSupport.lean):
  actual circle-weight necessity used to certify two-up/four-down support.

The connection uses existing proved sources, not an external seed premise.

## LLHH connection and symmetric multiplication sources

- [WeinbergFullSeed](../../../Physics/StandardModel/Operators/WeinbergFullSeed.lean):
  actual field projection/right inverse, LLHH seed, diagonal controls,
  invariant dressings and shifted all-Higgs support iff.
- [WeinbergSMInterface](../../../Physics/StandardModel/Operators/WeinbergSMInterface.lean):
  actual physical oneGenerationEquiv and coefficientEquiv_apply.
- [WeinbergResidualHom](../../../Physics/StandardModel/Operators/WeinbergResidualHom.lean):
  reconstruction and normalized factorization with fermionic exchange.
- [SymmetricCoefficientDressing](../../../Math/RepresentationTheory/SymmetricCoefficientDressing.lean):
  constructive symmetric multiplication/descent and invariant coefficient product.
- Unchanged mathlib MultilinearMap.domCoprod and TensorProduct.lift.equiv,
  existing SymmetricPowerDescent and SymmetricMultilinearProjection supply
  the typed algebraic multiplication primitives.

No external finite-generation theorem, VEV or nonzero premise is used.

## Eigenline reduction sources

- [HiggsEigenlineReduction](../../../Math/RepresentationTheory/HiggsEigenlineReduction.lean):
  local symmetric-line descent, full invariant coefficient transport,
  cancellation, periodic finite reduction and scalar-source support control.
- [SymmetricPowerDescent](../../../Math/RepresentationTheory/SymmetricPowerDescent.lean):
  actual arbitrary-degree symmetric quotient descent and tensor spanning.
- [InvariantCoefficientTransport](../../../Math/RepresentationTheory/InvariantCoefficientTransport.lean):
  both inverse identities for transport along actual representation equivalences.
- [ExternalInvariantTensor](../../../Math/RepresentationTheory/ExternalInvariantTensor.lean):
  tensorEquiv for the certified alternate-line carrier consumer.
- TauCeti.RepresentationTheory.CharacterTwist: inspected local pinned source;
  charTwist and tprodOfLinearCharacterEquivCharTwist are directly reused.
  LinearCharacter.Basic supplies ofLinearCharacter. The unchanged TauCeti
  revision is b9e2e182804073eb92718b68a9baf37df8e189bd, recorded in
  [lake-manifest.json](../../../lake-manifest.json).
- [HiggsEigenlineBoundary](../../../Physics/StandardModel/Operators/HiggsEigenlineBoundary.lean):
  uses the existing WeinbergFullSeed whole-content iff and LL count obstruction
  to refute residual-neutrality-only zero-Higgs support reduction on actual SM.

No new external finite-generation premise, dependency or weak-doublet
classification is introduced.

## Weak-doublet reduction sources

- [SymmetricDualPairing](../../../Math/RepresentationTheory/SymmetricDualPairing.lean):
  local independent symmetrization, actual symmetric dual pairing, covariance,
  diagonal formula and explicit irreducible perfectness consumer.
- [WeakDoubletScalars](../../../Math/RepresentationTheory/WeakDoubletScalars.lean):
  actual SU2 duality and exhaustive scalar coefficient classification.
- [WeakSingletHiggsReduction](../../../Math/RepresentationTheory/WeakSingletHiggsReduction.lean):
  full subgroup slice/factorization and both inverse coefficient transports.
- [WeakSingletHiggsSupport](../../../Physics/StandardModel/Operators/WeakSingletHiggsSupport.lean):
  actual SM weak inclusion, Higgs action, signed weak-singlet fields and exterior
  powers; no character-only field identification.
- TauCeti.RepresentationTheory.SU2.Irreducible: inspected local pinned source,
  isIrreducible_symPower is directly reused. Its Weight and SymmetricPower
  dependencies supply the actual weight basis and finrank_symPower. Revision
  b9e2e182804073eb92718b68a9baf37df8e189bd is unchanged in
  [lake-manifest.json](../../../lake-manifest.json). The proof is not inferred
  from Completeness's character recursion. No new external source premise.
- Existing SymmetricPowerDescent, SymmetricMultilinearProjection,
  InvariantTensorCurry, IrreducibleHomScalar and mathlib's multilinear
  piLinearMap and finite-dimensional injective/surjective theorem supply the
  algebraic primitives. General Clebsch-Gordan is not imported by this route.

## Remaining descent and weak-source investigation

- [TypedSymmetricPatternHom](../../../Math/RepresentationTheory/TypedSymmetricPatternHom.lean):
  actual symmetric field content with arbitrary equivariant output, normalized
  typed reconstruction, scalar/source currying and both inverse identities.
- [TwoBlockSymmetricDescent](../../../Math/RepresentationTheory/TwoBlockSymmetricDescent.lean):
  independent quotient descent for distinct Higgs and dual module types.
- [HiggsPatternDescent](../../../Physics/StandardModel/Operators/HiggsPatternDescent.lean):
  actual SM exterior source and original scalar species carrier consumer.
- Inspected pinned TauCeti `Algebra/Lie/Sl2/ClebschGordan.lean`: Lie-module
  decomposition only; no SU2 carrier equivalence imported or assumed.
- Inspected pinned TauCeti `RepresentationTheory/SU2/Completeness.lean`,
  `Irreducible.lean` and `Exhaustion.lean`: character recursion, actual
  symmetric-power irreducibility and continuous irreducible exhaustion have
  distinct hypotheses and conclusions. They do not supply the missing tensor
  carrier/group-action connection. Dependency revision remains unchanged.
- Existing TypedPatternSymmetrization and SymmetricPowerDescent are directly
  reused. Mathlib dependent multilinear reindexing and currySum were inspected
  as possible joining primitives, not claimed as a finished block equivalence.

## SU2-only tensor decomposition sources

- [SU2ClebschGordan](../../../Math/RepresentationTheory/SU2ClebschGordan.lean):
  constructed carrier decomposition, distinct degrees and exact dimension sum.
- [SU2SymmetricEmbeddings](../../../Math/RepresentationTheory/SU2SymmetricEmbeddings.lean)
  and [SU2DoubletDuality](../../../Math/RepresentationTheory/SU2DoubletDuality.lean):
  actual determinant-one tensor/form invariance, uniform nonzero evaluations
  and algebraic dual transport.
- [SymmetricPowerOperations](../../../Math/RepresentationTheory/SymmetricPowerOperations.lean):
  quotient multiplication, averaged splitting and group covariance.
- [DistinctIrreducibleAssembly](../../../Math/RepresentationTheory/Decomposition/DistinctIrreducibleAssembly.lean):
  proved independence via a hypothetical irreducible kernel constituent.
- Pinned TauCeti SU2 Irreducible/SymmetricPower: actual symmetric-power
  irreducibility and n+1 dimension are directly reused, as in the previous
  weak-singlet reduction. No dependency revision change.
- Pinned TauCeti Sl2 ClebschGordan: the private reflected arithmetic-progression
  proof of the sum of constituent dimensions was inspected and adapted locally.
  Its Lie-module carrier decomposition is neither imported nor assumed here.
- Pinned TauCeti RepresentationTheory.Irreducible: exists_isAtom_le and the
  atom/irreducible connection are reused in the assembly proof. Mathlib Schur,
  finite-dimensional injective/surjective and finite tensor rearrangement
  supply the other general algebraic steps.
- Existing SymmetricPowerDescent, SymmetricMultilinearProjection and
  SymmetricPowerLowDegree are directly reused. No Haar integration, topology
  or external literature theorem parameter is needed by this route.

## Full Higgs connection sources

- [TwoSpeciesPattern](../../../Math/RepresentationTheory/TwoSpeciesPattern.lean):
  species fibers, stabilizer decomposition and exact count/orbit correspondence.
- [TwoSpeciesSymmetricDescent](../../../Math/RepresentationTheory/TwoSpeciesSymmetricDescent.lean):
  dependent type transport, independent block symmetry and quotient descent.
- [TwoSpeciesCoefficientBridge](../../../Math/RepresentationTheory/TwoSpeciesCoefficientBridge.lean):
  actual covariance and both full/split coefficient transports.
- [CharacterTwistTransport](../../../Math/RepresentationTheory/CharacterTwistTransport.lean)
  and [TwistedSU2ClebschGordan](../../../Math/RepresentationTheory/TwistedSU2ClebschGordan.lean):
  generic character transport and proved full-group constituent actions.
- [SMHiggsConstituents](../../../Physics/StandardModel/Operators/SMHiggsConstituents.lean)
  and [FullHiggsCoefficientBridge](../../../Physics/StandardModel/Operators/FullHiggsCoefficientBridge.lean):
  actual weak/hypercharge projections, original scalar fields and exterior sources.
- Directly reused local TypedSymmetricPatternHom, TypedPatternSymmetrization,
  SymmetricPowerDescent, FiniteSpeciesExterior.permutation_of_counts,
  InvariantTensorCurry, InvariantCoefficientTransport and ExternalUnitEquivalence.
- Pinned mathlib dependent multilinear reindexing, currySum, module congruence,
  fiber permutation and finite cardinality APIs supply the generic primitives.
  Pinned TauCeti CharacterTwist supplies the twist representation definition;
  the symmetric/dual/tensor transports and application correspondence are proved
  locally. No new external source premise or dependency revision is introduced.

## Bounded SU(6) extraction sources

The [follow-up](su6-necessary-condition-results.md) uses repository proofs,
not new external literature: `FlavoredCyclicCoordinates.qque_allowed`,
`FlavoredCyclicSelection.allowed_total_iff` and `forbidden_total_iff`,
`CyclicWeightCoordinates.symmetricCharge_pair`, and
`SU6PhysicalIndexObstruction.pure_charge_equalities`. The exact source modules
are linked in the result. Existing `PhysicalChainSource`, `StandardSMUVFields`
and `ChargedAmbientRealization` were inspected to delimit the actual SU(6)
restriction, commuting action and mass-index bridge. The arbitrary unitary
ambient interface avoids assuming new finite branching data.

## Outside-class sample sources

The [sample contract](outside-class-sample-contract.md) uses repository assets:
`S3DipoleSelection.action`, `FiniteFlavorControls.a4` and its no-invariant-
functional theorem, `QqueSpinorExterior.hasModelExterior` / `exists_on_fields`,
`ExternalTensorDual.rightModelEquiv`, `StandardSMUVFields.gaugeEquiv`,
`SignedWeylTransposition.signedTranspositionSU` and `StandardSMGroup.hom`.
The older twisted-protection interface, compatibility and defect results were
read to avoid presenting previously tested candidates as new tests. No new
external literature, dependency or classification theorem is supplied.

## SM-preserving continuation sources

The [continuation](sm-preserving-sample-results.md) uses the existing actual
color probe and SM embedding, `PointwiseGaugeRemoval`, S3 permutation action,
physical qque exterior equivalence and `CommonIrreducible.all_zero_iff`.
Local pinned `TauCeti.RepresentationTheory.Symmetric.SignCharacter` supplies
the genuine sign character and swap values; pinned mathlib Maschke supplies
finite-group semisimplicity over C. Both libraries are already dependencies;
no pin changed. A standard-library exact signed-orbit script supplies finite
cross-checks only. No new external literature premise is introduced.
