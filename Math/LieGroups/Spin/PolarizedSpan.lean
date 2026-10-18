import Math.LieGroups.Spin.ExteriorComparison
import Mathlib.LinearAlgebra.Matrix.Dual

/-! The real compact Clifford generators span the complex polarized space.
Consequently complex-linear intertwining identities can be tested on them. -/

set_option autoImplicit false

namespace Math.CompactSpin.PolarizedSpan

noncomputable section

open Polarized ExteriorComparison
open scoped Matrix

def realVector (n : ℕ) (z : Fin n → ℂ) : RealSpace n :=
  (SpecialUnitaryRealification.coordinates n).symm z

theorem coordinates_realVector (n : ℕ) (z : Fin n → ℂ) :
    coordinates n (realVector n z) = (dotProductEquiv ℂ (Fin n) (star z), z) := by
  apply Prod.ext
  · apply LinearMap.ext
    intro w
    rw [coordinates_fst]
    simp only [realVector, LinearEquiv.apply_symm_apply]
    rfl
  · rw [coordinates_snd]
    exact (SpecialUnitaryRealification.coordinates n).apply_symm_apply z

theorem twice_axis (n : ℕ) (z : Fin n → ℂ) :
    coordinates n (realVector n z) - Complex.I • coordinates n (realVector n (Complex.I • z)) =
      (2 : ℂ) • ((0, z) : TauCeti.SplitEvenSpace ℂ n) := by
  simp only [coordinates_realVector]
  apply Prod.ext
  · apply LinearMap.ext
    intro w
    change star z ⬝ᵥ w - Complex.I * (star (Complex.I • z) ⬝ᵥ w) = (2 : ℂ) * 0
    simp [star_smul, smul_dotProduct, smul_eq_mul, ← mul_assoc]
  · funext i
    change z i - Complex.I * (Complex.I * z i) = 2 * z i
    calc
      _ = (1 - Complex.I ^ 2) * z i := by ring
      _ = _ := by rw [Complex.I_sq]; ring

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem linearMap_eq_zero (n : ℕ) (l : TauCeti.SplitEvenSpace ℂ n →ₗ[ℂ] E)
    (h : ∀ v, l (coordinates n v) = 0) : l = 0 := by
  have hw (z : Fin n → ℂ) : l (0, z) = 0 := by
    have hh : (2 : ℂ) • l (0, z) = 0 := by
      rw [← map_smul, ← twice_axis, map_sub, map_smul, h, h, smul_zero, sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have hf (f : Module.Dual ℂ (Fin n → ℂ)) : l (f, 0) = 0 := by
    obtain ⟨z, rfl⟩ := (dotProductEquiv ℂ (Fin n)).surjective f
    have hh := h (realVector n (star z))
    rw [coordinates_realVector, star_star] at hh
    have he : (dotProductEquiv ℂ (Fin n) z, star z) =
        (dotProductEquiv ℂ (Fin n) z, 0) + (0, star z) := by simp
    rw [he, map_add, hw, add_zero] at hh
    exact hh
  apply LinearMap.ext
  intro v
  have he : v = (v.1, 0) + (0, v.2) := by simp
  rw [he, map_add, hf, hw, add_zero, LinearMap.zero_apply]

theorem linearMap_ext (n : ℕ) (f g : TauCeti.SplitEvenSpace ℂ n →ₗ[ℂ] E)
    (h : ∀ v, f (coordinates n v) = g (coordinates n v)) : f = g := by
  apply sub_eq_zero.mp
  exact linearMap_eq_zero n (f - g) (fun v => by simp [h v])

end

end Math.CompactSpin.PolarizedSpan
