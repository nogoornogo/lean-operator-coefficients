import Math.RepresentationTheory.FourSlotAlternation
import Mathlib.Analysis.Complex.Circle

/-! Weight selection on pure exterior inputs. All hypotheses refer to the
actual representation action, independently of a chosen contraction basis. -/
namespace Math.ExteriorWeightSupport
set_option autoImplicit false
noncomputable section
open Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) {n : ℕ}

abbrev Coefficient := IntertwiningMap (rho.exteriorPower n) (Representation.trivial ℂ G ℂ)

theorem scalar_constraint (f : Coefficient rho) (g : G) (v : Fin n → V)
    (c : Fin n → ℂ) (hc : ∀ i, rho g (v i) = c i • v i) :
    ((∏ i, c i) - 1) * f (exteriorPower.ιMulti ℂ n v) = 0 := by
  let a := f.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ n)
  have h := IntertwiningMap.isIntertwining _ _ f g (exteriorPower.ιMulti ℂ n v)
  rw [Representation.exteriorPower_apply_ιMulti] at h
  change a (fun i => rho g (v i)) = a v at h
  simp only [hc] at h
  have hs := a.toMultilinearMap.map_smul_univ c v
  have h' := hs.symm.trans h
  change (∏ i, c i) * f (exteriorPower.ιMulti ℂ n v) =
    f (exteriorPower.ιMulti ℂ n v) at h'
  linear_combination h'

theorem vanish_of_scalar (f : Coefficient rho) (g : G) (v : Fin n → V)
    (c : Fin n → ℂ) (hc : ∀ i, rho g (v i) = c i • v i)
    (hprod : ∏ i, c i ≠ 1) : f (exteriorPower.ιMulti ℂ n v) = 0 :=
  (mul_eq_zero.mp (scalar_constraint rho f g v c hc)).resolve_left (sub_ne_zero.mpr hprod)

/-- A character of the full circle detects every nonzero integral weight.
No finite list of diagonal tests is substituted for U(1). -/
theorem circle_weight_zero (w : ℤ) (h : ∀ z : Circle, (z : ℂ) ^ w = 1) : w = 0 := by
  by_contra hw
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  have he := h (Circle.exp (Real.pi / w))
  rw [← Circle.coe_zpow, ← Circle.exp_intCast_mul] at he
  have hm : (w : ℝ) * (Real.pi / w) = Real.pi := by field_simp
  rw [hm, Circle.coe_exp, Complex.exp_pi_mul_I] at he
  norm_num at he

theorem prod_zpow {I : Type*} [Fintype I] (z : ℂ) (hz : z ≠ 0) (weight : I → ℤ) :
    (∏ i, z ^ weight i) = z ^ (∑ i, weight i) := by
  classical
  have hp (s : Finset I) : (∏ i ∈ s, z ^ weight i) = z ^ (∑ i ∈ s, weight i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        zpow_add₀ hz]
  exact hp Finset.univ

theorem circle_constraint (f : Coefficient rho) (v : Fin n → V)
    (weight : Fin n → ℤ) (circle : Circle → G)
    (hc : ∀ z i, rho (circle z) (v i) = (z : ℂ) ^ weight i • v i)
    (hf : f (exteriorPower.ιMulti ℂ n v) ≠ 0) : ∑ i, weight i = 0 := by
  apply circle_weight_zero
  intro z
  have h := scalar_constraint rho f (circle z) v (fun i => (z : ℂ) ^ weight i) (hc z)
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  rw [prod_zpow _ hz] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hf)

end
end Math.ExteriorWeightSupport
