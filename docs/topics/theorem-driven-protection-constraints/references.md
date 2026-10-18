# Proof Inputs and Their Roles

This first phase uses local checked theorem assets; no external literature
premise is introduced. Existing source/dependency pins remain unchanged.

| Input | Role |
| --- | --- |
| [Input-side API results](../prohibition-input-api/results.md) | Existing factor, scalar detection and constituent necessary conditions; avoid duplicating them |
| [Cyclic patterns](../../../Math/RepresentationTheory/ProhibitionPatterns.lean) | Actual scalar-action iff on a nontrivial carrier |
| [Cyclic characters](../../../Math/RepresentationTheory/CyclicCharge.lean) | Genuine formal character-line controls |
| [Qque constituent criterion](../../../Physics/StandardModel/Operators/QqueCommonIrreducible.lean) | Exact bounded-sector overlap criterion with its semisimplicity/field hypotheses |
| [Species surplus](../species-copy-surplus/README.md) | Existing physical surplus-to-nonzero implication and unequal-copy controls |
| [Physical surplus dossier](../../proof/current/applications/Physics/SPECIES_COPY_SURPLUS_QQUE.md) | Actual-sector presentation and mass obligations |
| [Standard chain](../../../GUT/Common/StandardChain/StandardChain.lean) | Existing ambient-group implication, not a new research prerequisite |
| [SU6 actual-index connection](../su6-light-placement-search/physical-index-results.md) | Regression exclusion and lesson: apply general constraints before enumeration |
| [Route inventory](../su6-light-placement-search/input-axis-theorem-map.md) | Overlapping application routes and unresolved input obligations |

References describe provenance and prerequisites. Merely linking a theorem
is not proof that a template satisfies its hypotheses.

## Existing-copy continuation

- [MatrixTenMass](../../../GUT/SU5/SelectionRules/MatrixTenMass.lean): actual
  p/q-copy fields and mass; `kernels`, `exists_actual_exterior`, and
  `rectangular_light_exterior` supply the physical implication.
- [New consumer](../../../GUT/SU5/SelectionRules/CopyCountProtectionConstraint.lean):
  reverses that existing implication to p<=q and connects parameter families.

## Extended family inputs

- [Earlier split-SU5 study](../../model-studies/su5-split-multiplets/results.md):
  Eq.(1) of 1706.08535v2 is previously supplied branching data, not a Lean equivalence.
- [Prior model evaluation](../proton-protection-model-checks/evaluation-result.md):
  explicit original 40/50 physical-adapter boundary.
- [Mass presentation constructor](../../../Physics/FieldTheory/Mass/SpeciesSectorPresentation.lean):
  requires actual sector equivalences and NoPairings; does not infer them from profiles.
- [Formal-character routines](../../../tools/su6-light-placement-search/check_small_branching.py):
  reused exact SU(3)/SU(2) character decomposition; no trusted oracle.

## Actual kernel construction assets

- [Actual five/ten](../../../GUT/SU5/Representations/Matter.lean) and
  [fundamental branching](../../../GUT/SU5/Branching/Fundamental.lean).
- Mathlib exterior powers, alternating curry, exterior multiplication and
  graded degree-two commutation under the unchanged dependency pin.
- TauCeti `LinearAlgebra.SymmetricPower.Basis.finrank_eq` supplies the actual
  symmetric quotient dimension; not a custom rank certificate.
- [SymmetricSquareDescent](../../../Math/RepresentationTheory/SymmetricSquareDescent.lean)
  descends the equivariant symmetric multilinear wedge coefficient.
- [CharacterExact](../../../Math/RepresentationTheory/Characters/CharacterExact.lean)
  derives actual trace identities from exact sequences.

## Selected-species extraction assets

- [Ten branching](../../../GUT/SU5/Branching/ExteriorSquare.lean): actual full-SM
  equivalence used to construct the hypercharge eigenbasis.
- [InvariantMassNormalForm](../../../GUT/SU5/SelectionRules/InvariantMassNormalForm.lean):
  existing actual Q/uc/ec and opposite hypercharge laws.
- TauCeti `SymmetricPower.map_basis_symmetricPower_of_apply_basis`: actual
  symmetric quotient action, under unchanged pins.
- Mathlib `ZMod.toCircle`, `injective_stdAddChar`, finite-dimensional
  injectivity/surjectivity and actual basis coordinates: exact phase exclusion.
- [Pairing interface](../../../Physics/FieldTheory/Mass/BipartiteNormalForm.lean):
  invariant bilinear pairings are maps into the actual dual.

## Actual 40 opposite-species assets

- [Fundamental branching](../../../GUT/SU5/Branching/Fundamental.lean):
  actual Five eigenbasis, with weights -2 and 3.
- [Ten eigenbasis](../../../GUT/SU5/Branching/ExoticHyperchargeBasis.lean):
  actual tensor source and exact phase separation reused for the original kernel.
- [Actual 40 kernel](../../../GUT/SU5/Representations/ExoticWedgeKernel.lean):
  source of the invariant subrepresentation and dual restriction.
- [SM epsilon uniqueness](../../../Physics/StandardModel/Gauge/SMEpsilonUniqueness.lean):
  used in the subsequent actual electron-singlet exclusion; it does not supply
  a complete 40 branching equivalence.

## Actual 40 color/weak extraction assets

- Mathlib multilinear alternatization, `AlternatingMap.coe_alternatization`
  and the exterior universal property construct the actual equivariant wedge
  section. The six permutations are enumerated by kernel-checked `decide`.
- [Weak contragredient](../../../Physics/StandardModel/Gauge/WeakContragredient.lean)
  and [hypercharge transport](../../../Physics/StandardModel/Gauge/HyperchargeTensorTransport.lean)
  identify selected source blocks without dropping their charges.
- [Epsilon uniqueness](../../../Physics/StandardModel/Gauge/SMEpsilonUniqueness.lean)
  proves actual color-invariant trilinear uniqueness. No external branching
  profile or character diagnostic enters the selected multiplicity theorem.
- [New result](forty-color-weak-results.md) lists source files and exact scope.

## Actual arbitrary-mass continuation

- [SpeciesCopySurplus](../../../Math/RepresentationTheory/Decomposition/SpeciesCopySurplus.lean):
  actual Hom-kernel equivalence and rank-nullity; no supplied branching input.
- [FiniteSpectrum](../../../Math/RepresentationTheory/Multiplicity/FiniteSpectrum.lean):
  explicit copies, product Hom equivalence and exact dimension formulas.
- [SymmetricMassIndex](../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean):
  original symmetric mass as an equivariant map to the dual, and its radical.
- [New actual mass result](exotic-mass-results.md): conjugate-copy scope and
  full five-species SM target. No new literature inputs or dependency changes.

## Full actual-family bridge

- [ExteriorEigenbasisTrace](../../../Math/LinearAlgebra/ExteriorEigenbasisTrace.lean)
  and [EigenbasisTrace](../../../Math/LinearAlgebra/EigenbasisTrace.lean): actual
  exterior and ordinary traces from proved eigenbasis action.
- [AbelianCharacterPolynomial](../../../Math/RepresentationTheory/Characters/AbelianCharacterPolynomial.lean):
  distinct-character linear independence and faithful integer-polynomial evaluation.
- [SymmetricMassIndex](../../../Physics/FieldTheory/Mass/SymmetricMassIndex.lean):
  actual radical dual-character equality without semisimplicity or topology.
- [UnitarySubrepresentationOrthogonality](../../../Math/RepresentationTheory/Unitary/UnitarySubrepresentationOrthogonality.lean):
  `rangeEquiv` is the algebraic injective-intertwiner/range identification;
  its use here needs no unitarity hypothesis.
- [QqueSpinorExterior](../../../Physics/StandardModel/Operators/QqueSpinorExterior.lean)
  and [FourSlotAlternation](../../../Math/RepresentationTheory/FourSlotAlternation.lean):
  physical spinor contraction, exterior descent and coefficient transport.
- [Existing spectrum-only endpoint](../exact-sm-spectrum-qque/results.md):
  context for the coefficient-side exclusion, not new independent coverage.
  The concrete gauge-only adapter proves its own actual-field inputs.

## Residual-action filtering inputs

- [NeutralQqueExterior](../../../Physics/StandardModel/Operators/NeutralQqueExterior.lean):
  existing physical neutral-character exterior and field transport; no new
  obstruction theorem is asserted by the filter.
- [AbelianProtonCharacter](../../../Physics/StandardModel/Operators/AbelianProtonCharacter.lean):
  actual character convention, with uc/ec left-chiral charge signs.
- [Residual filter result](residual-prefilter-results.md): application
  dictionaries, parameter preservation and full-family radical connection.
