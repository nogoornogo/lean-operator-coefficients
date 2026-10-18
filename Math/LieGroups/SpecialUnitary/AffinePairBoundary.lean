import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The real affine transvection method cannot supply nonconstant normalized SU(2) rows. -/
namespace Math.AffinePairBoundary
set_option autoImplicit false
noncomputable section
open Matrix

theorem normalized_pair (a b u v : ℂ)
    (h0 : Complex.normSq a + Complex.normSq b = 1)
    (hp : Complex.normSq (a+u) + Complex.normSq (b+v) = 1)
    (hm : Complex.normSq (a-u) + Complex.normSq (b-v) = 1) : u=0 ∧ v=0 := by
  rw [Complex.normSq_add, Complex.normSq_add] at hp
  rw [Complex.normSq_sub, Complex.normSq_sub] at hm
  have hu := Complex.normSq_nonneg u
  have hv := Complex.normSq_nonneg v
  constructor <;> apply Complex.normSq_eq_zero.mp <;> linarith

theorem row_norm (g : specialUnitaryGroup (Fin 2) ℂ) :
    Complex.normSq (g.val 0 0) + Complex.normSq (g.val 0 1) = 1 := by
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.star_def, Complex.mul_conj, Matrix.one_apply, ↓reduceIte] at he
  exact_mod_cast he

/-- This is a boundary for the affine route, not a prohibition of rational sampling. -/
theorem actual_row (g : ℝ → specialUnitaryGroup (Fin 2) ℂ) (a b u v : ℂ)
    (h0 : ∀ t : ℝ, (g t).val 0 0 = a + (t : ℂ)*u)
    (h1 : ∀ t : ℝ, (g t).val 0 1 = b + (t : ℂ)*v) : u=0 ∧ v=0 := by
  apply normalized_pair a b u v
  · simpa [h0, h1] using row_norm (g 0)
  · simpa [h0, h1] using row_norm (g 1)
  · simpa [h0, h1, sub_eq_add_neg] using row_norm (g (-1))

end
end Math.AffinePairBoundary
