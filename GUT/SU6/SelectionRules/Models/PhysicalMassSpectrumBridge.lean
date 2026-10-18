import Physics.FieldTheory.Mass.EquivariantMassIndex
import GUT.SU6.SelectionRules.Models.PhysicalLightSpectrumBridge

open Math

/-!
# Physical mass-index bridge for hypercharge character rigidity followed by standard charge-orbit bridge

An equivariant mass map over the product of the physical compact four-torus
and an ordinary Abelian residual group determines a virtual light character.
If its ultraviolet index is identified with the supplied `SU(6)` source and
its light index with the Standard Model target, faithful evaluation derives
the exact charge-resolved coefficient spectrum.

The strict ordinary specialization then feeds that one derived spectrum first
to hypercharge character rigidity, which fixes the hypercharge cocharacter, and only afterwards to the
standard standard charge-orbit bridge-to-Abelian proton-operator neutrality argument.
-/

namespace GUT
namespace PhysicalMassSpectrumBridge

open CompactEmbeddingClassification
open EquivariantMassIndex
open FiniteAbelianChargeSectors
open PhysicalChargeResolvedBridge
open PhysicalChargeResolvedEvaluation
open PhysicalRestrictionBridge
open StandardBranchProtonObstruction
open UnitaryVirtualRealization

noncomputable section

universe u

/-- A representation-level mass certificate for one physical resolved
character.  The model-specific fields state which ultraviolet representation
the mass map acts on and identify its unmatched light modes. -/
structure CharacterSource (H : Type u) [CommGroup H] where
  resolvedCharacter : PhysicalResolvedCharacter
    (FiniteAbelianChargeSectors.ChargeLabel H)
  leftSpace : Type
  [leftNormedAddCommGroup : NormedAddCommGroup leftSpace]
  [leftInnerProductSpace : InnerProductSpace ℂ leftSpace]
  [leftFiniteDimensional : FiniteDimensional ℂ leftSpace]
  rightSpace : Type
  [rightNormedAddCommGroup : NormedAddCommGroup rightSpace]
  [rightInnerProductSpace : InnerProductSpace ℂ rightSpace]
  [rightFiniteDimensional : FiniteDimensional ℂ rightSpace]
  leftRepresentation : Representation ℂ
    (PhysicalChargeResolvedEvaluation.CombinedGroup H) leftSpace
  rightRepresentation : Representation ℂ
    (PhysicalChargeResolvedEvaluation.CombinedGroup H) rightSpace
  leftUnitary : IsUnitaryRepresentation leftRepresentation
  rightUnitary : IsUnitaryRepresentation rightRepresentation
  massMap : Representation.IntertwiningMap leftRepresentation rightRepresentation
  ultravioletRepresentation : FiniteVirtualGroupRepresentation
    (PhysicalChargeResolvedEvaluation.CombinedGroup H)
  ultravioletCharacterModel :
    PhysicalChargeResolvedEvaluation.IsCharacterModel
      ultravioletRepresentation resolvedCharacter
  ultravioletMatchesResolved :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (ultravioletIndex
        (rhoV₀ := leftRepresentation) (rhoW₀ := rightRepresentation))
      ultravioletRepresentation
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges
    (FiniteAbelianChargeSectors.ChargeLabel H)
  singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ
  lightMatchesTarget :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex massMap rightUnitary)
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter generations charges singlets))

attribute [instance] CharacterSource.leftNormedAddCommGroup
attribute [instance] CharacterSource.leftInnerProductSpace
attribute [instance] CharacterSource.leftFiniteDimensional
attribute [instance] CharacterSource.rightNormedAddCommGroup
attribute [instance] CharacterSource.rightInnerProductSpace
attribute [instance] CharacterSource.rightFiniteDimensional

namespace CharacterSource

variable {H : Type u} [CommGroup H]

/-- The mass-index identity transports the light target to the modeled
ultraviolet character. -/
theorem sourceCharacterEquivalentTarget (S : CharacterSource H) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      S.ultravioletRepresentation
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter
          S.generations S.charges S.singlets)) := by
  have hUVTarget := ultravioletIndex_characterEquivalent_of_lightIndex
    S.massMap S.leftUnitary S.rightUnitary
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter
          S.generations S.charges S.singlets))
      S.lightMatchesTarget
  intro g
  exact (S.ultravioletMatchesResolved g).symm.trans (hUVTarget g)

/-- Hence the full local physical spectrum is a theorem, rather than an
independent coefficient field, once the two mass identifications are given. -/
theorem resolvedCharacter_eq_target (S : CharacterSource H) :
    S.resolvedCharacter =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  character_eq_of_models_of_characterEquivalent
    S.ultravioletCharacterModel
    (PhysicalChargeResolvedEvaluation.ofCharacter_isCharacterModel
      (exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets))
    S.sourceCharacterEquivalentTarget

theorem coefficientSpectrum (S : CharacterSource H) :
    IsExactSMOnlyPhysicalCoefficientSpectrum S.resolvedCharacter
      S.generations S.charges S.singlets :=
  IsExactSMOnlyPhysicalCoefficientSpectrum.of_resolvedCharacter_eq
    S.resolvedCharacter_eq_target

end CharacterSource

/-!
## Strict ordinary Abelian specialization
-/

/-- The charged `SU(6)` matter source, with every reconstructed physical
action retaining its invariant Hermitian inner product. -/
def ordinaryUnitaryVirtualSource
    {H : Type u} [CommGroup H]
    (m n : ℤ) (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    FiniteUnitaryVirtualRepresentation
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) :=
  PhysicalChargedCharacterBridge.sourceUnitaryRepresentation m n
    (ordinaryChargedSource matter)

/-- Canonical aggregate of the positive virtual coefficients. -/
def ordinaryPositiveRepresentation
    {H : Type u} [CommGroup H]
    (m n : ℤ) (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) :=
  FiniteUnitaryVirtualRepresentation.positive
    (ordinaryUnitaryVirtualSource m n matter)

/-- Canonical aggregate of the magnitudes of the negative virtual
coefficients. -/
def ordinaryNegativeRepresentation
    {H : Type u} [CommGroup H]
    (m n : ℤ) (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) :=
  FiniteUnitaryVirtualRepresentation.negative
    (ordinaryUnitaryVirtualSource m n matter)

/-!
## Chiral-index formulation of the physical spectrum
-/

/-- A strict ordinary `SU(6)` source whose low-energy chiral spectrum is
specified directly as an equality of virtual characters.  Unlike
`OrdinarySource` below, this does not choose separate representation
equivalences for the unmatched kernel and cokernel. -/
structure OrdinaryChiralIndexSource (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : ActualBlockCentralizer.WeakDoubletData
    (euclideanDefiningRestriction iota)
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  hyperchargeColor : ℤ
  hyperchargeWeak : ℤ
  massMap : Representation.IntertwiningMap
    (ordinaryPositiveRepresentation
      hyperchargeColor hyperchargeWeak matter).rho
    (ordinaryNegativeRepresentation
      hyperchargeColor hyperchargeWeak matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges
    (FiniteAbelianChargeSectors.ChargeLabel H)
  singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ
  lightIndexMatchesTarget :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex massMap
        (ordinaryNegativeRepresentation
          hyperchargeColor hyperchargeWeak matter).unitary)
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter generations charges singlets))

namespace OrdinaryChiralIndexSource

variable {H : Type u} [CommGroup H]

/-- Package the actual mass map and its chiral-index spectrum in the common
faithful character bridge. -/
def massCertificate (S : OrdinaryChiralIndexSource H) : CharacterSource H where
  resolvedCharacter := ordinaryPhysicalResolvedCharacter
    S.hyperchargeColor S.hyperchargeWeak S.matter
  leftSpace :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).V
  rightSpace :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).V
  leftRepresentation :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).rho
  rightRepresentation :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).rho
  leftUnitary :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
  rightUnitary :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
  massMap := S.massMap
  ultravioletRepresentation :=
    PhysicalChargedCharacterBridge.sourceProductRepresentation
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  ultravioletCharacterModel :=
    PhysicalChargedCharacterBridge.sourceProductRepresentation_isCharacterModel
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  ultravioletMatchesResolved :=
    PhysicalChargedCharacterBridge.canonicalUltravioletIndex_characterEquivalent
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  lightMatchesTarget := S.lightIndexMatchesTarget

/-- The character-level low-energy spectrum determines the full faithful
physical normal form. -/
theorem exactPhysicalSpectrum (S : OrdinaryChiralIndexSource H) :
    ordinaryPhysicalResolvedCharacter
        S.hyperchargeColor S.hyperchargeWeak S.matter =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  S.massCertificate.resolvedCharacter_eq_target

/-- hypercharge character rigidity fixes the physical cocharacter from the chiral-index spectrum. -/
theorem hyperchargePair_eq_standard (S : OrdinaryChiralIndexSource H) :
    S.hyperchargeColor = -2 ∧ S.hyperchargeWeak = 3 :=
  ordinary_eq_standard_of_exactResolved
    S.matter S.generations S.charges S.singlets
    S.hyperchargeColor S.hyperchargeWeak S.generations_ne
    S.exactPhysicalSpectrum

/-- After hypercharge character rigidity fixes the pair, the same chiral-index spectrum supplies standard charge-orbit bridge. -/
theorem standardCoefficientSpectrum (S : OrdinaryChiralIndexSource H) :
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum
      (StandardBlockChargeProjection.ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter)
      S.generations S.charges S.singlets :=
  ordinaryCoefficientSpectrum_of_exactResolved
    S.iota S.weakDoubletData S.matter S.generations
    S.charges S.singlets S.hyperchargeColor S.hyperchargeWeak
    S.generations_ne S.exactPhysicalSpectrum

/-- Package the derived standard charge-orbit bridge coefficient spectrum. -/
def toProjectedSource (S : OrdinaryChiralIndexSource H) :
    StandardBlockChargeProjection.PureSMOrdinaryAbelianProjectedSource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.charges
  singlets := S.singlets
  spectrum := S.standardCoefficientSpectrum

/-- standard charge-orbit bridge charge equalities derived from the character-level chiral index. -/
theorem physicalCharge_equalities (S : OrdinaryChiralIndexSource H) :
    SU5OrbitCompatible S.charges :=
  S.toProjectedSource.physicalCharge_equalities

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality for the character-level mass-index source. -/
theorem protonCharacters_eq_one (S : OrdinaryChiralIndexSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toProjectedSource.protonCharacters_eq_one

/-- Explicit finite-Abelian residual-symmetry specialization. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : OrdinaryChiralIndexSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.protonCharacters_eq_one

end OrdinaryChiralIndexSource

/-- A strict ordinary `SU(6)` source whose low-energy chiral spectrum is
identified by an actual equivariant mass certificate. -/
structure OrdinarySource (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : ActualBlockCentralizer.WeakDoubletData
    (euclideanDefiningRestriction iota)
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  hyperchargeColor : ℤ
  hyperchargeWeak : ℤ
  massMap : Representation.IntertwiningMap
    (ordinaryPositiveRepresentation
      hyperchargeColor hyperchargeWeak matter).rho
    (ordinaryNegativeRepresentation
      hyperchargeColor hyperchargeWeak matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges
    (FiniteAbelianChargeSectors.ChargeLabel H)
  singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ
  lightSpectrumEquiv :
    PhysicalLightSpectrumBridge.LightSpectrumEquiv massMap
      (ordinaryNegativeRepresentation
        hyperchargeColor hyperchargeWeak matter).unitary
      (exactSMWithSingletsResolvedCharacter generations charges singlets)

namespace OrdinarySource

variable {H : Type u} [CommGroup H]

/-- Forget the separate kernel/cokernel equivalences, retaining only their
induced equality of virtual light characters. -/
def toChiralIndexSource (S : OrdinarySource H) :
    OrdinaryChiralIndexSource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  matter := S.matter
  hyperchargeColor := S.hyperchargeColor
  hyperchargeWeak := S.hyperchargeWeak
  massMap := S.massMap
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  lightIndexMatchesTarget :=
    PhysicalLightSpectrumBridge.lightIndex_characterEquivalent_of_equiv
      S.massMap
      (ordinaryNegativeRepresentation
        S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
      (exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets)
      S.lightSpectrumEquiv

/-- Construct the general mass certificate using the actual reconstructed
product-group action on the original `SU(6)` charge sectors. -/
def massCertificate (S : OrdinarySource H) : CharacterSource H where
  resolvedCharacter := ordinaryPhysicalResolvedCharacter
    S.hyperchargeColor S.hyperchargeWeak S.matter
  leftSpace :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).V
  rightSpace :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).V
  leftRepresentation :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).rho
  rightRepresentation :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).rho
  leftUnitary :=
    (ordinaryPositiveRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
  rightUnitary :=
    (ordinaryNegativeRepresentation
      S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
  massMap := S.massMap
  ultravioletRepresentation :=
    PhysicalChargedCharacterBridge.sourceProductRepresentation
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  ultravioletCharacterModel :=
    PhysicalChargedCharacterBridge.sourceProductRepresentation_isCharacterModel
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  ultravioletMatchesResolved :=
    PhysicalChargedCharacterBridge.canonicalUltravioletIndex_characterEquivalent
      S.hyperchargeColor S.hyperchargeWeak
      (ordinaryChargedSource S.matter)
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  lightMatchesTarget :=
    PhysicalLightSpectrumBridge.lightIndex_characterEquivalent_of_equiv
      S.massMap
      (ordinaryNegativeRepresentation
        S.hyperchargeColor S.hyperchargeWeak S.matter).unitary
      (exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets)
      S.lightSpectrumEquiv

/-- The actual mass index supplies the single exact physical normal form
used by both hypercharge character rigidity and standard charge-orbit bridge. -/
theorem exactPhysicalSpectrum (S : OrdinarySource H) :
    ordinaryPhysicalResolvedCharacter
        S.hyperchargeColor S.hyperchargeWeak S.matter =
      exactSMWithSingletsResolvedCharacter
        S.massCertificate.generations S.massCertificate.charges
        S.massCertificate.singlets :=
  S.massCertificate.resolvedCharacter_eq_target

/-- hypercharge character rigidity first fixes the physical cocharacter to the standard pair. -/
theorem hyperchargePair_eq_standard (S : OrdinarySource H) :
    S.hyperchargeColor = -2 ∧ S.hyperchargeWeak = 3 :=
  ordinary_eq_standard_of_exactResolved
    S.matter S.massCertificate.generations S.massCertificate.charges
    S.massCertificate.singlets S.hyperchargeColor S.hyperchargeWeak
    S.massCertificate.generations_ne S.exactPhysicalSpectrum

/-- With the pair fixed, the same mass-derived spectrum becomes the local standard charge-orbit bridge
coefficient certificate. -/
theorem standardCoefficientSpectrum (S : OrdinarySource H) :
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum
      (StandardBlockChargeProjection.ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter)
      S.massCertificate.generations S.massCertificate.charges
      S.massCertificate.singlets :=
  ordinaryCoefficientSpectrum_of_exactResolved
    S.iota S.weakDoubletData S.matter S.massCertificate.generations
    S.massCertificate.charges S.massCertificate.singlets
    S.hyperchargeColor S.hyperchargeWeak
    S.massCertificate.generations_ne S.exactPhysicalSpectrum

/-- Package the derived standard charge-orbit bridge input without retaining a primitive spectrum
assumption. -/
def toProjectedSource (S : OrdinarySource H) :
    StandardBlockChargeProjection.PureSMOrdinaryAbelianProjectedSource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  matter := S.matter
  generations := S.massCertificate.generations
  generations_ne := S.massCertificate.generations_ne
  physicalCharges := S.massCertificate.charges
  singlets := S.massCertificate.singlets
  spectrum := S.standardCoefficientSpectrum

/-- standard charge-orbit bridge equalities obtained from the representation-level mass certificate. -/
theorem physicalCharge_equalities (S : OrdinarySource H) :
    SU5OrbitCompatible S.massCertificate.charges :=
  S.toProjectedSource.physicalCharge_equalities

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality for the mass-derived strict ordinary source. -/
theorem protonCharacters_eq_one (S : OrdinarySource H) :
    protonFirstCharacter S.massCertificate.charges = 1 ∧
      protonSecondCharacter S.massCertificate.charges = 1 :=
  S.toProjectedSource.protonCharacters_eq_one

/-- Explicit finite-Abelian residual-symmetry specialization. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : OrdinarySource H) :
    protonFirstCharacter S.massCertificate.charges = 1 ∧
      protonSecondCharacter S.massCertificate.charges = 1 :=
  S.protonCharacters_eq_one

end OrdinarySource

/-!
## Block-decomposition specialization
-/

/-- A strict ordinary source specified by a unitary decomposition into
unmatched light blocks and one common paired heavy block.  Its equivariant
mass map and both light-mode equivalences are derived rather than supplied. -/
structure BlockSource (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : ActualBlockCentralizer.WeakDoubletData
    (euclideanDefiningRestriction iota)
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  hyperchargeColor : ℤ
  hyperchargeWeak : ℤ
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges
    (FiniteAbelianChargeSectors.ChargeLabel H)
  singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ
  lightHeavyDecomposition : PhysicalLightSpectrumBridge.BlockDecomposition
    (ordinaryPositiveRepresentation hyperchargeColor hyperchargeWeak matter)
    (ordinaryNegativeRepresentation hyperchargeColor hyperchargeWeak matter)
    (exactSMWithSingletsResolvedCharacter generations charges singlets)

namespace BlockSource

variable {H : Type u} [CommGroup H]

/-- Construct the mass-map source from the stronger block-decomposition
certificate. -/
def toOrdinarySource (S : BlockSource H) : OrdinarySource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  matter := S.matter
  hyperchargeColor := S.hyperchargeColor
  hyperchargeWeak := S.hyperchargeWeak
  massMap := S.lightHeavyDecomposition.massMap
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  lightSpectrumEquiv := S.lightHeavyDecomposition.lightSpectrumEquiv

/-- The block decomposition derives the exact physical resolved spectrum. -/
theorem exactPhysicalSpectrum (S : BlockSource H) :
    ordinaryPhysicalResolvedCharacter
        S.hyperchargeColor S.hyperchargeWeak S.matter =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  S.toOrdinarySource.exactPhysicalSpectrum

/-- hypercharge character rigidity fixes the cocharacter of a block-decomposed physical source. -/
theorem hyperchargePair_eq_standard (S : BlockSource H) :
    S.hyperchargeColor = -2 ∧ S.hyperchargeWeak = 3 :=
  S.toOrdinarySource.hyperchargePair_eq_standard

/-- The block decomposition supplies the standard charge-orbit bridge coefficient spectrum after hypercharge character rigidity. -/
theorem standardCoefficientSpectrum (S : BlockSource H) :
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum
      (StandardBlockChargeProjection.ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter)
      S.generations S.charges S.singlets :=
  S.toOrdinarySource.standardCoefficientSpectrum

/-- Package the derived standard charge-orbit bridge input. -/
def toProjectedSource (S : BlockSource H) :
    StandardBlockChargeProjection.PureSMOrdinaryAbelianProjectedSource H :=
  S.toOrdinarySource.toProjectedSource

/-- standard charge-orbit bridge charge equalities derived from the unitary light-heavy
decomposition. -/
theorem physicalCharge_equalities (S : BlockSource H) :
    SU5OrbitCompatible S.charges :=
  S.toOrdinarySource.physicalCharge_equalities

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality for a block-decomposed source. -/
theorem protonCharacters_eq_one (S : BlockSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toOrdinarySource.protonCharacters_eq_one

/-- Explicit finite-Abelian residual-symmetry specialization. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : BlockSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.protonCharacters_eq_one

end BlockSource

end

end PhysicalMassSpectrumBridge
end GUT
