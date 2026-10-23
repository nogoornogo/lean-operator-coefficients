import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Unitary operators commuting with an antiunitary quaternionic structure.
The data restrict to invariant subspaces without a choice of coordinates. -/

set_option autoImplicit false

namespace Math.QuaternionicSpectral

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

structure Data where
  q : E →ₛₗ[starRingEnd ℂ] E
  square : ∀ v, q (q v) = -v
  pairing : ∀ v w, inner ℂ (q v) (q w) = star (inner ℂ v w)
  t : E →ₗ[ℂ] E
  unitary : ∀ v w, inner ℂ (t v) (t w) = inner ℂ v w
  intertwines : ∀ v, q (t v) = t (q v)

variable {E}

namespace Data

variable (D : Data E)

theorem q_norm (v : E) : ‖D.q v‖ = ‖v‖ := by
  have hh : ‖D.q v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, D.pairing]
    exact Complex.conj_re _
  nlinarith [norm_nonneg (D.q v), norm_nonneg v]

theorem t_norm (v : E) : ‖D.t v‖ = ‖v‖ := by
  have hh : ‖D.t v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, D.unitary]
  nlinarith [norm_nonneg (D.t v), norm_nonneg v]

theorem q_orthogonal (v : E) : inner ℂ v (D.q v) = 0 := by
  have hh := D.pairing v (D.q v)
  rw [D.square, inner_neg_right, ← inner_conj_symm] at hh
  change -star (inner ℂ v (D.q v)) = star (inner ℂ v (D.q v)) at hh
  have hz : star (inner ℂ v (D.q v)) = 0 := by linear_combination -hh / 2
  exact star_injective (hz.trans (star_zero _).symm)

theorem q_skew_pairing (v w : E) :
    inner ℂ v (D.q w) = -star (inner ℂ (D.q v) w) := by
  have hh := D.pairing (D.q v) w
  rw [D.square, inner_neg_left] at hh
  exact neg_eq_iff_eq_neg.mp hh

theorem q_eigen {v : E} {z : Circle} (he : D.t v = (z : ℂ) • v) :
    D.t (D.q v) = ((z⁻¹ : Circle) : ℂ) • D.q v := by
  rw [← D.intertwines, he, map_smulₛₗ]
  rw [Circle.coe_inv_eq_conj]

def restrict (S : Submodule ℂ E) (ht : ∀ v ∈ S, D.t v ∈ S)
    (hq : ∀ v ∈ S, D.q v ∈ S) : Data S where
  q := D.q.restrict hq
  square v := Subtype.ext (D.square v)
  pairing v w := D.pairing v w
  t := D.t.restrict ht
  unitary v w := D.unitary v w
  intertwines v := Subtype.ext (D.intertwines v)

theorem exists_unit_eigenvector [FiniteDimensional ℂ E] [Nontrivial E] :
    ∃ (z : Circle) (v : E), ‖v‖ = 1 ∧ D.t v = (z : ℂ) • v := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue D.t
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  let w := (‖v‖ : ℂ)⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hvn
  have hwe : D.t w = c • w := by
    rw [show w = (‖v‖ : ℂ)⁻¹ • v from rfl, map_smul, hv.apply_eq_smul]
    exact smul_comm _ _ _
  have hcn : ‖c‖ = 1 := by
    have hh := D.t_norm w
    rw [hwe, norm_smul, hwn, mul_one] at hh
    exact hh
  exact ⟨⟨c, mem_sphere_zero_iff_norm.mpr hcn⟩, w, hwn, hwe⟩

end Data

end

end Math.QuaternionicSpectral
