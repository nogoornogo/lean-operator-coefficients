import Physics.FieldTheory.Mass.EquivariantMassIndex
import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalCharacterBridge
import GUT.SU6.SelectionRules.Models.StandardPhysicalSpectrumBridge

open Math

/-!
# From an equivariant mass map to the standard chiral spectrum

This module connects the character index of an actual equivariant mass map
to the existing standard charge-orbit bridge source interface.  It separates two model-dependent facts:

* the ultraviolet source-minus-target representation is the reconstructed
  finite virtual representation of the supplied `SU(6)` matter;
* the unmatched kernel/cokernel representation is the stated low-energy
  Standard Model spectrum plus gauge singlets.

Given those representation-level certificates, the equality of the
charge-resolved Laurent coefficients is derived by the already checked
faithful evaluator.  It is no longer an independent coefficient assumption.
-/

namespace GUT
namespace StandardMassSpectrumBridge

open CompactEmbeddingClassification
open EquivariantMassIndex
open FiniteAbelianChargeSectors
open PhysicalRestrictionBridge
open StandardAbelianCharge
open StandardBranchProtonObstruction
open StandardPhysicalCharacterBridge
open StandardPhysicalSource
open StandardSMCharacterTarget

noncomputable section

universe u

/-- A standard-branch source together with an actual equivariant mass map.
The two character-equivalence fields are the remaining model-specific
identifications of the ultraviolet fields and the light spectrum. -/
structure Source (H : Type u) [CommGroup H] where
  matter : FiniteChargedContinuousUnitarySource
    (FiniteAbelianChargeSectors.ChargeLabel H)
  centralCharacter : H →* Circle
  leftSpace : Type
  [leftNormedAddCommGroup : NormedAddCommGroup leftSpace]
  [leftInnerProductSpace : InnerProductSpace ℂ leftSpace]
  [leftFiniteDimensional : FiniteDimensional ℂ leftSpace]
  rightSpace : Type
  [rightNormedAddCommGroup : NormedAddCommGroup rightSpace]
  [rightInnerProductSpace : InnerProductSpace ℂ rightSpace]
  [rightFiniteDimensional : FiniteDimensional ℂ rightSpace]
  leftRepresentation : Representation ℂ
    (StandardSMCharacterTarget.CombinedGroup H) leftSpace
  rightRepresentation : Representation ℂ
    (StandardSMCharacterTarget.CombinedGroup H) rightSpace
  leftUnitary : IsUnitaryRepresentation leftRepresentation
  rightUnitary : IsUnitaryRepresentation rightRepresentation
  massMap : Representation.IntertwiningMap leftRepresentation rightRepresentation
  ultravioletMatchesMatter :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (ultravioletIndex
        (rhoV₀ := leftRepresentation) (rhoW₀ := rightRepresentation))
      (sourceProductRepresentation centralCharacter matter)
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (FiniteAbelianChargeSectors.ChargeLabel H)
  singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ
  lightMatchesTarget :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex massMap rightUnitary)
      (targetWithSinglets generations charges singlets)

attribute [instance] Source.leftNormedAddCommGroup
attribute [instance] Source.leftInnerProductSpace
attribute [instance] Source.leftFiniteDimensional
attribute [instance] Source.rightNormedAddCommGroup
attribute [instance] Source.rightInnerProductSpace
attribute [instance] Source.rightFiniteDimensional

namespace Source

variable {H : Type u} [CommGroup H]

/-- The mass-index theorem transports the identified light target back to
the reconstructed ultraviolet matter character. -/
theorem matterCharacterEquivalentTarget (S : Source H) :
    IsSMTargetCharacterEquivalent
      (sourceProductRepresentation S.centralCharacter S.matter)
      S.generations S.charges S.singlets := by
  have hUVTarget := ultravioletIndex_characterEquivalent_of_lightIndex
    S.massMap S.leftUnitary S.rightUnitary
      (targetWithSinglets S.generations S.charges S.singlets)
      S.lightMatchesTarget
  intro g
  exact (S.ultravioletMatchesMatter g).symm.trans (hUVTarget g)

/-- Faithfulness of the product-group evaluator now derives the entire
charge-resolved chiral character. -/
theorem resolvedCharacter_eq_target (S : Source H) :
    S.matter.resolvedCharacter (centralDegreeCharge S.centralCharacter) =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  exactResolvedCharacter_of_characterEquivalent
    S.generations S.charges S.singlets
    (sourceProductRepresentation_isCharacterModel
      S.centralCharacter S.matter)
    S.matterCharacterEquivalentTarget

/-- In particular, the representation-level mass certificate supplies the
local coefficient formulation consumed by standard charge-orbit bridge. -/
theorem coefficientSpectrum (S : Source H) :
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum
      (S.matter.resolvedCharacter
        (centralDegreeCharge S.centralCharacter))
      S.generations S.charges S.singlets :=
  StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum.of_resolvedCharacter_eq
    S.resolvedCharacter_eq_target

/-- Package the derived character equality in the pre-existing standard charge-orbit bridge source
interface. -/
def toPureSMCharacterSource (S : Source H) :
    StandardSMCharacterTarget.PureSMCharacterSource H where
  matter := S.matter
  centralCharge := centralDegreeCharge S.centralCharacter
  combinedRepresentation :=
    sourceProductRepresentation S.centralCharacter S.matter
  characterModel := sourceProductRepresentation_isCharacterModel
    S.centralCharacter S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent := S.matterCharacterEquivalentTarget

/-- standard charge-orbit bridge gives the two charge-orbit equalities directly from the mass
certificate. -/
theorem charge_equalities (S : Source H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toPureSMCharacterSource.charge_equalities

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality: both proton-operator characters are trivial.  No
continuous anomaly equation is used. -/
theorem protonCharacters_eq_one (S : Source H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toPureSMCharacterSource.protonCharacters_eq_one

/-- Explicit finite-Abelian specialization of the mass-index bridge. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : Source H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.protonCharacters_eq_one

end Source

end

end StandardMassSpectrumBridge
end GUT
