import GUT.SU6.SelectionRules.Models.ContinuousWeylFamilyModel
import GUT.SU6.SelectionRules.Models.ContinuousWeylFullMass

/-!
# A nonlinear source for the existing nonzero fifteen-mode mass

A neutral scalar with a quadratic coupling and VEV one recovers the entire
old mass model. This proves non-vacuity of the new source class, not a new
full-SU(6) invariant scalar geometry, an exact SM stabilizer, or dynamics.
-/

set_option autoImplicit false

namespace GUT.WeylMassFamilyBenchmark

noncomputable section

open ContinuousWeylFamilyModel WeylMassFamily InvariantWeylMass
open StandardSMCharacterTarget ConcreteSU6PhysicalTarget

def model (H : Type*) [CommGroup H] : Model H :=
  Model.ofMassAsPower (ContinuousWeylFullMass.model H) 2

variable {H : Type*} [CommGroup H]

theorem toMassModel : (model H).toMassModel = ContinuousWeylFullMass.model H :=
  Model.ofMassAsPower_toMassModel _ _

theorem bare_mass_zero : (model H).sector.bareMass.form = 0 := rfl

theorem vacuum_one : (model H).sector.vacuum.value = (1 : ℂ) := rfl

set_option maxHeartbeats 800000 in
theorem family_at_one_nonzero : (model H).sector.family.toFun (1 : ℂ) ≠ 0 :=
  Model.ofMassAsPower_at_one_nonzero (ContinuousWeylFullMass.model H) 2
    (ContinuousWeylFullMass.mass_nonzero (H := H))

set_option maxHeartbeats 800000 in
theorem family_not_additive :
    (model H).sector.family.Nonadditive :=
  Model.ofMassAsPower_quadratic_not_additive (ContinuousWeylFullMass.model H)
    (ContinuousWeylFullMass.mass_nonzero (H := H))

theorem mass_nonzero : (model H).sector.mass.form ≠ 0 := by
  change (model H).toMassModel.mass.form ≠ 0
  rw [toMassModel]
  exact ContinuousWeylFullMass.mass_nonzero

theorem radical_finrank : Module.finrank ℂ (model H).sector.mass.radical.toSubmodule = 15 := by
  change Module.finrank ℂ (model H).toMassModel.mass.radical.toSubmodule = 15
  rw [toMassModel]
  exact ContinuousWeylFullMass.radical_finrank

theorem lightSpectrum : PhysicalWeylZeroModeSupport.lightSpectrum (model H).toMassModel.toPhysical =
    exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 := by
  rw [toMassModel]
  exact ContinuousWeylFullMass.lightSpectrum

def supportedInvariantOperator : StandardModelLocalOperator.SupportedInvariantOperator
    (PhysicalWeylZeroModeSupport.lightSpectrum (model H).toMassModel.toPhysical) :=
  (model H).supportedInvariantOperator (by change (0 : ℤ) < 1; norm_num)

/-- Change only the VEV, leaving the nonzero quadratic coupling intact. -/
def zeroVacuumSector :=
  { (model H).sector with vacuum := DiracYukawaMass.InvariantVacuum.zero }

theorem zeroVacuum_family : (zeroVacuumSector (H := H)).family = (model H).sector.family := rfl

theorem zeroVacuum_mass : (zeroVacuumSector (H := H)).mass =
    SymmetricMass.zero _ := by
  exact Model.ofMassAsPower_zeroVacuum (ContinuousWeylFullMass.model H) 1

theorem zeroVacuum_radical :
    (zeroVacuumSector (H := H)).mass.radical.toSubmodule = ⊤ := by
  rw [zeroVacuum_mass]
  exact SymmetricMass.radical_zero

theorem exists_nonlinear_sm_radical (H : Type*) [CommGroup H] :
    ∃ M : Model H, M.generations = 1 ∧ M.sector.bareMass.form = 0 ∧
      M.sector.family.Nonadditive ∧
      M.sector.mass.form ≠ 0 ∧ Module.finrank ℂ M.sector.mass.radical.toSubmodule = 15 ∧
      PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ⟨model H, rfl, bare_mass_zero, family_not_additive,
    mass_nonzero, radical_finrank, lightSpectrum⟩

end
end GUT.WeylMassFamilyBenchmark
