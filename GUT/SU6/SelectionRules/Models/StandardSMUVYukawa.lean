import GUT.SU6.Yukawa.UnitarySymmetricScalar
import GUT.SU6.SelectionRules.Models.StandardSMOrdinaryMass

/-!
# A full-SU(6) scalar completion of the 15-mode benchmark

The scalar multiplet is the continuous unitary model of all symmetric
bilinear forms on the actual 27-dimensional UV matter representation.
Its Yukawa family is independent of the selected mass. The constructed
VEV reproduces the existing full-SM-invariant mass, with zero bare mass.
This is a nonminimal existence completion, not vacuum dynamics.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GUT.StandardSMUVYukawa

noncomputable section

open StandardSMUVFields InvariantWeylMass WeylYukawaMass
open StandardSMGaugeTensor (GaugeGroup)

attribute [local irreducible] ConcreteWeylBenchmark.matter

def scalar := UnitarySymmetricScalar.model uvRho uv_jointlyContinuous

def yukawa := UnitarySymmetricScalar.yukawa uvRho uv_jointlyContinuous

def tensor := yukawa.tensorIntertwiner

def bareMass := SymmetricMass.zero uvRho

theorem bare_mass_zero : bareMass.form = 0 := rfl

variable (H : Type*) [CommGroup H]

def vacuum : scalar.V := UnitarySymmetricScalar.vacuum uvRho uv_jointlyContinuous
  (StandardSMGroup.withResidual H) (StandardSMUVMass.mass H)

theorem vacuum_fixed (g : GaugeGroup × H) :
    scalar.rho (StandardSMGroup.withResidual H g) (vacuum H) = vacuum H :=
  UnitarySymmetricScalar.vacuum_fixed uvRho uv_jointlyContinuous _ _ g

theorem unbroken_le_stabilizer : (StandardSMGroup.withResidual H).range ≤
    vacuumStabilizer scalar.rho (vacuum H) := by
  rintro _ ⟨g, rfl⟩
  exact vacuum_fixed H g

theorem vacuum_mass_form : yukawa.toLinearMap (vacuum H) = (StandardSMUVMass.mass H).form :=
  UnitarySymmetricScalar.yukawa_vacuum uvRho uv_jointlyContinuous _ _

theorem vacuum_nonzero : vacuum H ≠ 0 :=
  UnitarySymmetricScalar.vacuum_nonzero uvRho uv_jointlyContinuous _ _
    (StandardSMUVMass.mass_nonzero H)

def mass := atVacuumOn bareMass yukawa (StandardSMGroup.withResidual H)
  (vacuum H) (vacuum_fixed H)

theorem mass_eq : mass H = StandardSMUVMass.mass H :=
  UnitarySymmetricScalar.inducedMass_eq uvRho uv_jointlyContinuous _ _

theorem mass_nonzero : (mass H).form ≠ 0 := by
  rw [mass_eq]
  exact StandardSMUVMass.mass_nonzero H

theorem radical_finrank : Module.finrank ℂ (mass H).radical.toSubmodule = 15 := by
  rw [mass_eq]
  exact StandardSMUVMass.radical_finrank H

/-- The same VEV coefficient gives the mass on the canonical field carrier. -/
theorem ordinary_form : (StandardSMOrdinaryMass.mass H).form =
    (yukawa.toLinearMap (vacuum H)).compl₁₂
      (StandardSMOrdinaryFields.physicalEquiv H).toLinearEquiv.toLinearMap
      (StandardSMOrdinaryFields.physicalEquiv H).toLinearEquiv.toLinearMap := by
  rw [vacuum_mass_form, StandardSMOrdinaryMass.mass_form_eq,
    StandardSMOrdinaryMass.fullMass_form_eq]
  rfl

def zeroVacuumMass := atVacuumOn bareMass yukawa (StandardSMGroup.withResidual H)
  0 (fun _ => map_zero _)

theorem zeroVacuumMass_eq : zeroVacuumMass H =
    SymmetricMass.zero (uvRho.comp (StandardSMGroup.withResidual H)) := by
  simp [zeroVacuumMass, atVacuumOn, bareMass, SymmetricMass.zero]

theorem zeroVacuum_radical_finrank :
    Module.finrank ℂ (zeroVacuumMass H).radical.toSubmodule = 27 := by
  rw [zeroVacuumMass_eq, SymmetricMass.radical_zero]
  simpa using uv_finrank

theorem yukawa_nonzero : yukawa.toLinearMap ≠ 0 :=
  UnitarySymmetricScalar.yukawa_nonzero uvRho uv_jointlyContinuous
    (StandardSMGroup.withResidual Unit) (StandardSMUVMass.mass Unit)
    (StandardSMUVMass.mass_nonzero Unit)

theorem tensor_nonzero : tensor.toLinearMap ≠ 0 :=
  UnitarySymmetricScalar.tensor_nonzero uvRho uv_jointlyContinuous
    (StandardSMGroup.withResidual Unit) (StandardSMUVMass.mass Unit)
    (StandardSMUVMass.mass_nonzero Unit)

end

end GUT.StandardSMUVYukawa
