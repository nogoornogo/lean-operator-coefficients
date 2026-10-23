import GUT.SU6.SelectionRules.StandardBranch.StandardWeylMassSource

open Physics

open Math

/-!
# Audit of the canonical all-left-handed source

Nonnegative multiplicities and strict commuting actions construct the field
representation; UV character identification is a theorem, not a model field.
The standard-branch model still requires its infrared dual SM target.
-/

set_option autoImplicit false

namespace GUT.AuditStandardWeylMassSource

open StandardWeylMassSource StandardSMCharacterTarget
open InvariantWeylMass PhysicalRestrictionBridge
open StandardPhysicalCharacterBridge (sourceProductRepresentation chargedProductRepresentation)

example {H : Type*} [CommGroup H]
    (R : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation)
    (q : ChargeLabel H) :
    Module.finrank ℂ (fields [{ coeff := 1, rep := R, offset := q }]).V =
      Module.finrank ℂ R.V := by
  have h := fields_character [{ coeff := 1, rep := R, offset := q }]
    (by
      intro s hs
      rcases List.mem_singleton.mp hs with rfl
      norm_num) (1 : CombinedGroup H)
  have hc : (Module.finrank ℂ (fields [{ coeff := 1, rep := R, offset := q }]).V : ℂ) =
      (Module.finrank ℂ R.V : ℂ) := by
    simpa [sourceProductRepresentation, FiniteVirtualGroupRepresentation.character,
      VirtualGroupSummand.character, ActualGroupRepresentation.character,
      chargedProductRepresentation, Representation.char_one] using h
  exact_mod_cast hc

example {H : Type*} [CommGroup H]
    (R : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation)
    (action : FiniteAbelianChargeSectors.CommutingAction H R) :
    Nonempty (SymmetricMass
      (ordinaryFields [{ coeff := 1, rep := R, action := action }]).rho) :=
  ⟨SymmetricMass.zero _⟩

example (M : StandardWeylModel (Multiplicative (ZMod 2))) :
    StandardBranchProtonObstruction.protonFirst M.charges = 0 ∧
      StandardBranchProtonObstruction.protonSecond M.charges = 0 :=
  M.proton_functionals_eq_zero

#print axioms UnitaryVirtualRealization.FiniteUnitaryVirtualRepresentation.positive_character_of_nonnegative
#print axioms sectorUnitaryRepresentation
#print axioms fields_character
#print axioms ordinaryChargedSource_nonnegative
#print axioms ordinaryFields
#print axioms ordinaryFields_character
#print axioms ordinaryFields_proton_functionals_eq_zero
#print axioms StandardWeylModel.proton_functionals_eq_zero

end GUT.AuditStandardWeylMassSource
