import Physics.StandardModel.Spectrum.ExactSMSpectrum
import TauCeti.RepresentationTheory.FDRep
import Mathlib.Tactic

/-! An actual one-generation SM character probe detects hypercharge reversal. -/
namespace GUT.HyperchargeReversalProbe
set_option autoImplicit false
noncomputable section
open Representation ExactSMSpectrum StandardSMGaugeTensor SMEpsilonTensor

def phase : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩
def probe : GaugeGroup := (1, 1, phase)

theorem character_of_hypercharge {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (rho : Representation ℂ GaugeGroup V) (y : ℤ)
    (hy : HasHypercharge rho y) (z : Circle) :
    rho.character (1, 1, z) = ((z ^ y : Circle) : ℂ) * Module.finrank ℂ V := by
  have he : rho (1, 1, z) = ((z ^ y : Circle) : ℂ) • LinearMap.id := by
    ext v
    exact hy z v
  change LinearMap.trace ℂ V (rho (1, 1, z)) = _
  rw [he, map_smul, LinearMap.trace_id]
  rfl

theorem generation_character (z : Circle) :
    generation.character (1, 1, z) =
      6 * (z : ℂ) ^ (1 : ℤ) + 3 * (z : ℂ) ^ (-4 : ℤ) +
      3 * (z : ℂ) ^ (2 : ℤ) + 2 * (z : ℂ) ^ (-3 : ℤ) + (z : ℂ) ^ (6 : ℤ) := by
  simp only [generation, char_prod]
  rw [character_of_hypercharge quark 1 quark_hypercharge,
    character_of_hypercharge upRight.dual (-4) upLeft_hypercharge,
    character_of_hypercharge downRight.dual 2 downLeft_hypercharge,
    character_of_hypercharge lepton (-3) lepton_hypercharge,
    character_of_hypercharge electronRight.dual 6 electronLeft_hypercharge]
  simp [Quark, Color, Weak, Module.finrank_tensorProduct]
  ring

theorem generation_probe_nonzero : generation.character probe - generation.dual.character probe ≠ 0 := by
  rw [char_dual]
  simp only [probe, Prod.inv_mk, inv_one]
  rw [generation_character, generation_character]
  have hp : (phase : ℂ) = Complex.I := rfl
  have hi : ((phase⁻¹ : Circle) : ℂ) = -Complex.I := by
    rw [Circle.coe_inv_eq_conj, hp]
    simp
  rw [hp, hi]
  norm_num [zpow_neg, Complex.inv_def, Complex.ext_iff]

end
end GUT.HyperchargeReversalProbe
