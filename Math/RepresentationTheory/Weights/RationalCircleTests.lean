import Math.RepresentationTheory.Weights.IntegralTorusTests
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! An exact circle test with rational real and imaginary coordinates. -/
namespace Math.RationalCircleTests
set_option autoImplicit false
noncomputable section

def sample : Circle := ⟨(3+4*Complex.I)/5, by
  change (3+4*Complex.I)/5 ∈ Metric.sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm]
  rw [norm_div]
  have h : ‖(3+4*Complex.I : ℂ)‖ = 5 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)).mp
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [h]
  norm_num⟩

theorem trace_sample : (sample : ℂ) + ((sample⁻¹ : Circle) : ℂ) = (6/5 : ℂ) := by
  rw [Circle.coe_inv_eq_conj]
  apply Complex.ext <;> norm_num [sample, Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem not_integral_trace : ¬ IsIntegral ℤ (6/5 : ℂ) := by
  intro h
  have hr : IsIntegral ℤ (6/5 : ℚ) :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp (by simpa using h)
  obtain ⟨k,hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hr
  have hk' : (k : ℚ) = 6/5 := hk
  have he : (5 : ℚ) * k = 6 := by rw [hk']; norm_num
  have hi : (5 : ℤ)*k=6 := by exact_mod_cast he
  omega

theorem pow_ne_one (n : ℕ) (hn : 0 < n) : (sample : ℂ)^n ≠ 1 := by
  intro h
  have hi : IsIntegral ℤ (sample : ℂ) := IsIntegral.of_pow hn
    (by rw [h]; exact isIntegral_one)
  have hj : IsIntegral ℤ ((sample⁻¹ : Circle) : ℂ) := IsIntegral.of_pow hn (by
    rw [Circle.coe_inv, inv_pow, h, inv_one]
    exact isIntegral_one)
  exact not_integral_trace (trace_sample ▸ hi.add hj)

theorem zpow_ne_one (k : ℤ) (hk : k ≠ 0) : (sample : ℂ)^k ≠ 1 := by
  cases k with
  | ofNat n =>
    have hn : 0 < n := Nat.pos_of_ne_zero (by intro h; subst n; exact hk rfl)
    change (sample : ℂ)^(n : ℤ) ≠ 1
    rw [zpow_natCast]
    exact pow_ne_one n hn
  | negSucc n =>
    intro h
    have he := congrArg (fun z : ℂ => z⁻¹) h
    simp only [zpow_negSucc, inv_inv, inv_one] at he
    exact pow_ne_one (n+1) (Nat.succ_pos n) he

open Representation BoundedTorusWeights
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) (torus : Circle →* G)

theorem invariant (hi : IntegralTorusTests.Integral rho torus) (f : Module.Dual ℂ V)
    (hf : ∀ x, f (rho (torus sample) x) = f x) : ∀ z x, f (rho (torus z) x) = f x := by
  intro z x
  have hx : x ∈ Submodule.span ℂ {v : V | ∃ w : ℤ, Eigen rho torus w v} := by rw [hi]; trivial
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,hw⟩ := hv
    by_cases hz : w=0
    · simp [hw z,hz]
    · have he := hf v
      rw [hw sample, map_smul, smul_eq_mul] at he
      have hzero : f v = 0 := by
        have hc : ((sample : ℂ)^w-1) * f v = 0 := by linear_combination he
        exact (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr (zpow_ne_one w hz))
      simp [hw z,hzero]
  | zero => simp
  | add v w _ _ hv hw => simp [hv,hw]
  | smul c v _ hv => simp [hv]

theorem conjugate_invariant (hi : IntegralTorusTests.Integral rho torus)
    (c : G) (f : Module.Dual ℂ V)
    (hf : ∀ x, f (rho (c * torus sample * c⁻¹) x) = f x) :
    ∀ z x, f (rho (c * torus z * c⁻¹) x) = f x := by
  let h := f.comp (rho c)
  have hs : ∀ x, h (rho (torus sample) x) = h x := by
    intro x
    have he := hf (rho c x)
    simpa [h, ← Module.End.mul_apply, ← map_mul, mul_assoc] using he
  have hz := invariant rho torus hi h hs
  intro z x
  have he := hz z (rho c⁻¹ x)
  simpa [h, ← Module.End.mul_apply, ← map_mul, mul_assoc] using he

end
end Math.RationalCircleTests
