import GUT.SU6.SelectionRules.Models.StandardSMUVYukawa
import Physics.FieldTheory.Yukawa.YukawaClassification
import Physics.FieldTheory.Mass.ScaledMassSpectrum

/-! An actual full-SU(6) Yukawa family, evaluated before its exact radical
is identified. The scalar multiplet is the existing nonminimal one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6GeneratedMassFamily
noncomputable section
open Representation InvariantWeylMass WeylYukawaMass StandardSMUVFields
open StandardSMGaugeTensor (GaugeGroup)

attribute [local irreducible] ConcreteWeylBenchmark.matter

def allCouplings :=
  YukawaClassification.endomorphismEquiv StandardSMUVYukawa.scalar.rho uvRho
    (UnitarySymmetricScalar.algebraEquiv uvRho uv_jointlyContinuous)

def coupling (y : ℂ) := YukawaClassification.scalarMultiple
  StandardSMUVYukawa.scalar.rho uvRho StandardSMUVYukawa.yukawa y

variable (H : Type*) [CommGroup H]

def vacuum (t : ℂ) := t • StandardSMUVYukawa.vacuum H

theorem vacuum_fixed (t : ℂ) (g : GaugeGroup × H) :
    StandardSMUVYukawa.scalar.rho (StandardSMGroup.withResidual H g) (vacuum H t) =
      vacuum H t := by
  simp only [vacuum, map_smul, StandardSMUVYukawa.vacuum_fixed]

def mass (y t : ℂ) : SymmetricMass (StandardSMUVMass.rho H) :=
  atVacuumOn StandardSMUVYukawa.bareMass (coupling y) (StandardSMGroup.withResidual H)
    (vacuum H t) (vacuum_fixed H t)

theorem mass_eq (y t : ℂ) :
    mass H y t = ScaledMassSpectrum.mass (StandardSMUVMass.mass H) (y * t) := by
  apply SymmetricMass.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  change 0 + y * StandardSMUVYukawa.yukawa.toLinearMap
    (t • StandardSMUVYukawa.vacuum H) x z =
      (y * t) * (StandardSMUVMass.mass H).form x z
  rw [map_smul, StandardSMUVYukawa.vacuum_mass_form]
  change 0 + y * (t * (StandardSMUVMass.mass H).form x z) = _
  ring

theorem light_preserved (y t : ℂ) (x : StandardSMUVMass.ZeroModes H) :
    x.val ∈ (mass H y t).radical.toSubmodule := by
  rw [mass_eq, SymmetricMass.mem_radical]
  intro z
  change (y * t) * (StandardSMUVMass.mass H).form x.val z = 0
  rw [(SymmetricMass.mem_radical _ _).mp x.property z, mul_zero]

def lightEquiv (y t : ℂ) (h : y * t ≠ 0) :
    Representation.Equiv (mass H y t).radical.toRepresentation
      (StandardSMFullGaugeMass.lightRho (neutralCharges H)) := by
  rw [mass_eq]
  exact (ScaledMassSpectrum.radicalEquiv (StandardSMUVMass.mass H) (y * t) h).trans
    (StandardSMUVMass.lightEquiv H)

theorem zero_mass (y t : ℂ) (h : y * t = 0) :
    mass H y t = SymmetricMass.zero (StandardSMUVMass.rho H) := by
  rw [mass_eq, h, ScaledMassSpectrum.zero_mass]

def zeroLightEquiv (y t : ℂ) (h : y * t = 0) :
    Representation.Equiv (mass H y t).radical.toRepresentation (StandardSMUVMass.rho H) := by
  rw [zero_mass H y t h]
  exact SymmetricMass.zeroRadicalEquiv _

theorem radical_finrank (y t : ℂ) :
    Module.finrank ℂ (mass H y t).radical.toSubmodule = if y * t = 0 then 27 else 15 := by
  split_ifs with h
  · rw [(zeroLightEquiv H y t h).toLinearEquiv.finrank_eq]
    exact uv_finrank
  · rw [(lightEquiv H y t h).toLinearEquiv.finrank_eq]
    exact StandardSMFullGaugeMass.light_finrank

theorem mass_nonzero_iff (y t : ℂ) : (mass H y t).form ≠ 0 ↔ y ≠ 0 ∧ t ≠ 0 := by
  constructor
  · intro hn
    apply mul_ne_zero_iff.mp
    intro hz
    apply hn
    rw [zero_mass H y t hz]
    rfl
  · rintro ⟨hy, ht⟩
    rw [mass_eq]
    exact ScaledMassSpectrum.form_nonzero _ _ (mul_ne_zero hy ht)
      (StandardSMUVMass.mass_nonzero H)

theorem fifteen_iff (y t : ℂ) :
    Module.finrank ℂ (mass H y t).radical.toSubmodule = 15 ↔ y ≠ 0 ∧ t ≠ 0 := by
  by_cases h : y * t = 0
  · have hn : ¬ (y ≠ 0 ∧ t ≠ 0) := fun k => (mul_ne_zero k.1 k.2) h
    simp [radical_finrank, h, hn]
  · have hn := mul_ne_zero_iff.mp h
    simp [radical_finrank, h, hn.1, hn.2]

theorem light_character (y t : ℂ) (h : y * t ≠ 0) (g : GaugeGroup × H) :
    (mass H y t).radical.toRepresentation.character g =
      (StandardSMFullGaugeMass.lightRho (neutralCharges H)).character g :=
  congrFun (Representation.char_iso (lightEquiv H y t h)) g

theorem original_mass : mass H 1 1 = StandardSMUVYukawa.mass H := by
  have h := mass_eq H 1 1
  rw [one_mul] at h
  exact h.trans ((ScaledMassSpectrum.one_mass _).trans (StandardSMUVYukawa.mass_eq H).symm)

theorem coupling_off (t : ℂ) : Module.finrank ℂ (mass H 0 t).radical.toSubmodule = 27 := by
  simp [radical_finrank]

theorem vacuum_off (y : ℂ) : Module.finrank ℂ (mass H y 0).radical.toSubmodule = 27 := by
  simp [radical_finrank]

end
end GUT.SU6GeneratedMassFamily
