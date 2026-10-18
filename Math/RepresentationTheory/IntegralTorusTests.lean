import Math.RepresentationTheory.BoundedTorusWeights
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Pi.Irrational

/-! A single exact infinite-order circle element tests integral torus invariance. -/
namespace Math.IntegralTorusTests
set_option autoImplicit false
noncomputable section
open Representation BoundedTorusWeights
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) (torus : Circle →* G)

def Integral : Prop := Submodule.span ℂ {v : V | ∃ w : ℤ, Eigen rho torus w v} = ⊤

def sample : Circle := Circle.exp 1

/-- Exact integer-power separation; the pinned SU2 Weight proof supplies the same argument. -/
theorem sample_powers : Function.Injective (fun w : ℤ => (sample : ℂ)^w) := by
  intro m n hmn
  have h : (sample^m : Circle) = sample^n :=
    Subtype.ext (by simpa only [Circle.coe_zpow] using hmn)
  rw [sample, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, mul_one, mul_one] at h
  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp h
  rcases eq_or_ne k 0 with rfl | hk0
  · have he : (m : ℝ) = n := by simpa using hk
    exact_mod_cast he
  · refine absurd ?_ ((irrational_pi.intCast_mul (m := 2*k) (by omega)).ne_int (m-n))
    push_cast
    linear_combination -hk

theorem sample_ne_one (w : ℤ) (hw : w ≠ 0) : (sample : ℂ)^w ≠ 1 := by
  intro h
  apply hw
  apply sample_powers
  simpa using h

theorem of_bounded (N : ℕ) (h : Bounded rho torus N) : Integral rho torus := by
  apply top_unique
  rw [← h]
  apply Submodule.span_mono
  rintro v ⟨w,_,_,he⟩
  exact ⟨w,he⟩

theorem of_basis {I : Type*} (b : Module.Basis I ℂ V) (w : I → ℤ)
    (h : ∀ i, Eigen rho torus (w i) (b i)) : Integral rho torus := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨w i,h i⟩

theorem invariant (hi : Integral rho torus) (f : Module.Dual ℂ V)
    (hf : ∀ x, f (rho (torus sample) x) = f x) :
    ∀ z x, f (rho (torus z) x) = f x := by
  intro z x
  have hx : x ∈ Submodule.span ℂ {v : V | ∃ w : ℤ, Eigen rho torus w v} := by
    rw [hi]; trivial
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,hw⟩ := hv
    by_cases hz : w=0
    · simp [hw z,hz]
    · have he := hf v
      rw [hw sample, map_smul, smul_eq_mul] at he
      have hzero : f v = 0 := by
        have hc : ((sample : ℂ)^w-1) * f v = 0 := by linear_combination he
        exact (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr (sample_ne_one w hz))
      simp [hw z,hzero]
  | zero => simp
  | add v w _ _ hv hw => simp [hv,hw]
  | smul c v _ hv => simp [hv]

/-- Fixed conjugation does not require a separately chosen basis or degree bound. -/
theorem conjugate_invariant (hi : Integral rho torus) (c : G) (f : Module.Dual ℂ V)
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

theorem of_surjective {U : Type*} [AddCommGroup U] [Module ℂ U]
    (sigma : Representation ℂ G U) (e : IntertwiningMap rho sigma)
    (he : Function.Surjective e) (hi : Integral rho torus) : Integral sigma torus := by
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr he, LinearMap.range_eq_map, ← hi, Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨x,⟨w,hw⟩,rfl⟩
  refine ⟨w,?_⟩
  intro z
  change sigma (torus z) (e x) = (z : ℂ)^w • e x
  rw [← e.isIntertwining _ _ (torus z), hw z, map_smul]

open scoped TensorProduct in
theorem tensor {U : Type*} [AddCommGroup U] [Module ℂ U]
    (sigma : Representation ℂ G U) (hr : Integral rho torus)
    (hs : Integral sigma torus) : Integral (rho.tprod sigma) torus := by
  let S := Submodule.span ℂ {v : V ⊗[ℂ] U | ∃ w : ℤ, Eigen (rho.tprod sigma) torus w v}
  have ht (x : V) (y : U) : x ⊗ₜ[ℂ] y ∈ S := by
    have hx : x ∈ Submodule.span ℂ {v : V | ∃ w : ℤ, Eigen rho torus w v} := by rw [hr]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w,hw⟩ := hx
      have hy : y ∈ Submodule.span ℂ {v : U | ∃ k : ℤ, Eigen sigma torus k v} := by rw [hs]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k,hk⟩ := hy
        exact Submodule.subset_span ⟨w+k, eigen_tmul rho torus sigma hw hk⟩
      | zero => simp
      | add y z _ _ hy hz => simpa [TensorProduct.tmul_add] using S.add_mem hy hz
      | smul c y _ hy => simpa [TensorProduct.tmul_smul] using S.smul_mem c hy
    | zero => simp
    | add x z _ _ hx hz => simpa [TensorProduct.add_tmul] using S.add_mem hx hz
    | smul c x _ hx => simpa [TensorProduct.smul_tmul'] using S.smul_mem c hx
  change S = ⊤
  apply Submodule.eq_top_iff'.mpr
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul x y => exact ht x y
  | add x y hx hy => exact S.add_mem hx hy

theorem scalar (w : ℤ) (he : ∀ z x, rho (torus z) x = (z : ℂ)^w • x) :
    Integral rho torus := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact Submodule.subset_span ⟨w,fun z => he z x⟩

end
end Math.IntegralTorusTests