import GUT.SU6.SelectionRules.StandardBranch.StandardWeylMassSource
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator
import GUT.SU6.SelectionRules.StandardBranch.StandardAbelianCharge
import Mathlib.Tactic

open Physics

open Math

/-!
# Conditional UV supported-operator witness for the standard Weyl mass source

Constructs a `SupportedInvariantOperator` from a `StandardWeylModel` by
combining the UV source support with the dual-index charge constraints and
the proved trivial proton characters. The support assumption is on UV fields,
not on the mass radical. This does not close the zero-mode support bridge.
-/

set_option autoImplicit false

namespace GUT.StandardWeylSupportedOperator

open StandardBranchProtonObstruction
open StandardAbelianCharge
open StandardModelLocalOperator
open StandardWeylMassSource
open StandardWeylDualTarget
open StandardSMCharacterTarget (ChargeLabel)
open StandardPhysicalSource (FiniteChargedContinuousUnitarySource)
open StandardPhysicalCharacterBridge (sourceProductRepresentation_character
    chargedProductRepresentation)
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)
open PhysicalChargeResolvedBridge (ordinaryChargedSource)
open FiniteAbelianChargeSectors (centralDegreeCharge
    protonFirstCharacter protonSecondCharacter
    protonFirstCharacter_eq_one_of_eq_zero
    protonSecondCharacter_eq_one_of_eq_zero)

noncomputable section

variable {H : Type*} [CommGroup H]

/-- The resolved UV character of the ordinary matter source. -/
def pUV (M : StandardWeylModel H) : ResolvedCharacter (ChargeLabel H) :=
  (ordinaryChargedSource M.matter).resolvedCharacter
    (centralDegreeCharge (1 : H →* Circle))

/-- The resolved UV character is Weyl-invariant. -/
theorem pUV_isWeylInvariant (M : StandardWeylModel H) :
    ResolvedWeylInvariant (pUV M) :=
  (ordinaryChargedSource M.matter).resolvedCharacter_isWeylInvariant
    (centralDegreeCharge (1 : H →* Circle))

/-- The standard Weyl model forces SU5OrbitCompatible on the stored charges. -/
theorem su5OrbitCompatible (M : StandardWeylModel H) :
    SU5OrbitCompatible M.charges :=
  su5OrbitCompatible_of_mass_dual_target
    M.mass (ordinaryFields M.matter).unitary
    ((ordinaryChargedSource M.matter).resolvedCharacter
      (centralDegreeCharge (1 : H →* Circle)))
    ((ordinaryChargedSource M.matter).resolvedCharacter_isWeylInvariant
      (centralDegreeCharge (1 : H →* Circle)))
    (fun x h =>
      (ordinaryFields_character M.matter M.nonnegative
        (Multiplicative.ofAdd x, h)).trans
      (sourceProductRepresentation_character (1 : H →* Circle)
        (ordinaryChargedSource M.matter) x h))
    M.generations M.generations_ne M.charges M.singlets M.lightTarget

/-- The first proton character is trivial. -/
theorem protonFirstCharacter_eq_one (M : StandardWeylModel H) :
    protonFirstCharacter M.charges = 1 :=
  protonFirstCharacter_eq_one_of_eq_zero M.charges M.proton_functionals_eq_zero.1

/-- The second proton character is trivial. -/
theorem protonSecondCharacter_eq_one (M : StandardWeylModel H) :
    protonSecondCharacter M.charges = 1 :=
  protonSecondCharacter_eq_one_of_eq_zero M.charges M.proton_functionals_eq_zero.2

/-- The two standard proton characters are both trivial. -/
theorem protonCharacters_eq_one (M : StandardWeylModel H) :
    protonFirstCharacter M.charges = 1 ∧ protonSecondCharacter M.charges = 1 :=
  ⟨protonFirstCharacter_eq_one M, protonSecondCharacter_eq_one M⟩

/-- Charge-profile equalities from Weyl invariance. -/
theorem pUV_chargeProfilesEqual (M : StandardWeylModel H) :
    quarkProfile (pUV M) = upProfile (pUV M) ∧
    quarkProfile (pUV M) = electronProfile (pUV M) ∧
    downProfile (pUV M) = leptonProfile (pUV M) :=
  sm_charge_profiles_equal (pUV M) (pUV_isWeylInvariant M)

/-- Hypothesis that the quark and down orbit profiles are nonzero at the model's charges. -/
def nonzeroOrbitProfiles (M : StandardWeylModel H) : Prop :=
  quarkProfile (pUV M) M.charges.quark ≠ 0 ∧
    downProfile (pUV M) M.charges.down ≠ 0

/-- Charges-supported certificate under the UV resolved character. -/
theorem chargesSupported (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    ChargesSupported (pUV M) M.charges := by
  rcases pUV_chargeProfilesEqual M with ⟨hQU, hQE, hDL⟩
  rcases hOrbit with ⟨hTen, hBarFive⟩
  rcases su5OrbitCompatible M with ⟨hqu, hqe, hdl⟩
  refine ⟨hTen, ?_, hBarFive, ?_, ?_⟩
  · rw [← hQU, ← hqu]
    exact hTen
  · rw [← hDL, ← hdl]
    exact hBarFive
  · rw [← hQE, ← hqe]
    exact hTen

/-- A SupportedInvariantOperator witness for the qque class. -/
def supportedQqueWitness (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    SupportedInvariantOperator (pUV M) :=
  StandardModelLocalOperator.supportedQque M.charges
    (chargesSupported M hOrbit)
    (protonFirstCharacter_eq_one_of_eq_zero M.charges M.proton_functionals_eq_zero.1)

/-- A SupportedInvariantOperator witness for the duql class. -/
def supportedDuqlWitness (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    SupportedInvariantOperator (pUV M) :=
  StandardModelLocalOperator.supportedDuql M.charges
    (chargesSupported M hOrbit)
    (protonSecondCharacter_eq_one_of_eq_zero M.charges M.proton_functionals_eq_zero.2)

/-- The model supports at least one canonical invariant operator. -/
theorem not_forbidsEverySupportedStandardOperator (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    ¬ ForbidsEverySupportedStandardOperator (pUV M) :=
  (supportedQqueWitness M hOrbit).not_forbidsEverySupportedStandardOperator

/-- The model supports at least one admissible Delta-B = 1 local operator. -/
theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (pUV M) :=
  (supportedQqueWitness M hOrbit).not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite-Abelian form. -/
theorem finiteAbelian_not_forbidsEverySupportedStandardOperator
    [Finite H] (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    ¬ ForbidsEverySupportedStandardOperator (pUV M) :=
  not_forbidsEverySupportedStandardOperator M hOrbit

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (M : StandardWeylModel H)
    (hOrbit : nonzeroOrbitProfiles M) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (pUV M) :=
  not_forbidsEverySupportedPhysicalDeltaBOneOperator M hOrbit

end

end GUT.StandardWeylSupportedOperator
