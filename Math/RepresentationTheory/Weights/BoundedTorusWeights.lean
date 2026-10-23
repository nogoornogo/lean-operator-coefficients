import Math.RepresentationTheory.Exterior.ExteriorWeightSupport
import Math.RepresentationTheory.SU2.WeakDoubletScalars

/-! Algebraic torus bounds from spanning eigenvectors. No continuity,
unitarity or semisimplicity of the source representation is assumed. -/
namespace Math.BoundedTorusWeights
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (a : Representation ℂ G V) (torus : Circle →* G)

def Eigen (w : ℤ) (v : V) : Prop :=
  ∀ z : Circle, a (torus z) v = (z : ℂ) ^ w • v

def Bounded (N : ℕ) : Prop :=
  Submodule.span ℂ {v : V | ∃ w : ℤ, -(N : ℤ) ≤ w ∧ w ≤ N ∧ Eigen a torus w v} = ⊤

/-- Restrict the acting group before transporting bounded eigenvectors.
Keeping the carrier abstract avoids unfolding a concrete statistical source. -/
theorem bounded_comp {K : Type*} [Group K] (j : K →* G)
    (t : Circle →* K) (N : ℕ) (h : Bounded a (j.comp t) N) :
    Bounded (a.comp j) t N := h

theorem of_basis {I : Type*} (b : Module.Basis I ℂ V) (w : I → ℤ) (N : ℕ)
    (hb : ∀ i, Eigen a torus (w i) (b i))
    (hw : ∀ i, -(N : ℤ) ≤ w i ∧ w i ≤ N) : Bounded a torus N := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨w i, (hw i).1, (hw i).2, hb i⟩

theorem dual_basis_eigen {I : Type*} [Fintype I] [DecidableEq I] (b : Module.Basis I ℂ V)
    (w : I → ℤ) (hb : ∀ i, Eigen a torus (w i) (b i)) (i : I) :
    Eigen a.dual torus (-w i) (b.dualBasis i) := by
  classical
  intro z
  apply b.ext
  intro j
  change b.dualBasis i (a (torus z)⁻¹ (b j)) =
    (z : ℂ)^(-w i) * b.dualBasis i (b j)
  rw [← map_inv, hb j z⁻¹, map_smul, smul_eq_mul,
    Module.Basis.dualBasis_apply_self]
  by_cases hij : j=i
  · subst j; simp
  · simp [hij]

theorem eigen_tmul {U : Type*} [AddCommGroup U] [Module ℂ U]
    (b : Representation ℂ G U) {w k : ℤ} {x : V} {y : U}
    (hx : Eigen a torus w x) (hy : Eigen b torus k y) :
    Eigen (a.tprod b) torus (w+k) (x ⊗ₜ[ℂ] y) := by
  intro z
  rw [Representation.tprod_apply, TensorProduct.map_tmul, hx z, hy z,
    TensorProduct.smul_tmul_smul,
    zpow_add₀ z.coe_ne_zero]

theorem bounded_of_surjective {U : Type*} [AddCommGroup U] [Module ℂ U]
    (b : Representation ℂ G U) (f : IntertwiningMap a b)
    (hs : Function.Surjective f) (N : ℕ) (ha : Bounded a torus N) :
    Bounded b torus N := by
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr hs, LinearMap.range_eq_map, ← ha, Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨x, ⟨w, hlo, hhi, he⟩, rfl⟩
  refine ⟨w, hlo, hhi, ?_⟩
  intro z
  change b (torus z) (f x) = (z : ℂ)^w • f x
  rw [← f.isIntertwining _ _ (torus z), he z, map_smul]

theorem eigen_pair_zero {w k : ℤ} {v : V} {f : Module.Dual ℂ V}
    (hv : Eigen a torus w v) (hf : Eigen a.dual torus k f) (hwk : w+k ≠ 0) :
    f v = 0 := by
  by_contra hn
  apply hwk
  apply ExteriorWeightSupport.circle_weight_zero
  intro z
  have he := congrArg (fun phi : Module.Dual ℂ V => phi (a (torus z) v)) (hf z)
  have hi : a (torus z)⁻¹ (a (torus z) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  change f (a (torus z)⁻¹ (a (torus z) v)) =
    (z : ℂ)^k * f (a (torus z) v) at he
  rw [hi, hv z, map_smul, smul_eq_mul] at he
  have hm : (z : ℂ)^(w+k) * f v = f v := by
    rw [zpow_add₀ z.coe_ne_zero]
    calc
      _ = (z : ℂ)^k * ((z : ℂ)^w * f v) := by ring
      _ = f v := he.symm
  exact (mul_right_cancel₀ hn (hm.trans (one_mul (f v)).symm))

theorem dual_eigen_zero (N : ℕ) (ha : Bounded a torus N) (k : ℤ)
    (hk : (N : ℤ) < k ∨ k < -(N : ℤ)) (f : Module.Dual ℂ V)
    (hf : Eigen a.dual torus k f) : f = 0 := by
  apply LinearMap.ext
  intro v
  change f v = 0
  have hv : v ∈ Submodule.span ℂ
      {v : V | ∃ w : ℤ, -(N : ℤ) ≤ w ∧ w ≤ N ∧ Eigen a torus w v} := by
    rw [ha]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hlo, hhi, he⟩ := hx
    exact eigen_pair_zero a torus he hf (by rcases hk with hk | hk <;> omega)
  | zero => exact map_zero f
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem high_spin_hom_zero (a : Representation ℂ WeakDoubletScalars.Group V)
    (N m : ℕ) (ha : Bounded a TauCeti.SU2.torusHom N) (hm : N < m)
    (f : IntertwiningMap (WeakDoubletScalars.doublet.symmetricPower m) a.dual) :
    f = 0 := by
  rcases IsIrreducible.injective_or_eq_zero f with hi | he
  · have hv : Eigen a.dual TauCeti.SU2.torusHom (m : ℤ)
        (f (TauCeti.SU2.weightBasis m (Fin.last m))) := by
      intro z
      have he : (WeakDoubletScalars.doublet.symmetricPower m) (TauCeti.SU2.torusHom z)
          (TauCeti.SU2.weightBasis m (Fin.last m)) =
          (z : ℂ)^(m : ℤ) • TauCeti.SU2.weightBasis m (Fin.last m) := by
        rw [WeakDoubletScalars.symmetricPower_eq,
          TauCeti.SU2.symPower_torusHom_weightBasis, TauCeti.SU2.weight_last]
      rw [← f.isIntertwining _ _ (TauCeti.SU2.torusHom z)]
      rw [he, map_smul]
    have hz := dual_eigen_zero a TauCeti.SU2.torusHom N ha (m : ℤ)
      (Or.inl (by exact_mod_cast hm)) _ hv
    have hzero := hi (hz.trans (map_zero f).symm)
    exact False.elim ((TauCeti.SU2.weightBasis m).ne_zero (Fin.last m) hzero)
  · exact he

end
end Math.BoundedTorusWeights
