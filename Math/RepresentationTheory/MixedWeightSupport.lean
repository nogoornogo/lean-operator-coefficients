import Math.RepresentationTheory.ExteriorWeightSupport
import TauCeti.RepresentationTheory.SymmetricPower
import Math.LinearAlgebra.SymmetricPowerLowDegree

/-! Scalar weight selection for independent exterior/symmetric coefficients.
The boson representation is supplied, not assumed trivial. -/
namespace Math.MixedWeightSupport
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G A B : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B) {n m : ℕ}

abbrev Coefficient := IntertwiningMap ((a.exteriorPower n).tprod (b.symmetricPower m))
  (Representation.trivial ℂ G ℂ)

/-- The zero-boson degree retains exactly the independently defined exterior input. -/
def zeroBosonEquiv (n : ℕ) :
    Representation.Equiv ((a.exteriorPower n).tprod (b.symmetricPower 0)) (a.exteriorPower n) :=
  (Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl ℂ _) SymmetricPowerLowDegree.zeroEquiv)
    (by
      intro g
      apply TensorProduct.ext'
      intro u w
      change (a.exteriorPower n g u) ⊗ₜ[ℂ]
        SymmetricPowerLowDegree.zeroEvaluation (b.symmetricPower 0 g w) =
        (a.exteriorPower n g u) ⊗ₜ[ℂ] SymmetricPowerLowDegree.zeroEvaluation w
      have h := LinearMap.congr_fun
        ((SymmetricPowerLowDegree.representationZeroEquiv b).isIntertwining' g) w
      exact congrArg ((a.exteriorPower n g u) ⊗ₜ[ℂ] ·) h)).trans
    (Representation.TensorProduct.rid ℂ (a.exteriorPower n))

/-- A single boson is transported without imposing an extra statistical relation. -/
def oneBosonEquiv (n : ℕ) :
    Representation.Equiv ((a.exteriorPower n).tprod (b.symmetricPower 1))
      ((a.exteriorPower n).tprod b) where
  toLinearEquiv := TensorProduct.congr (LinearEquiv.refl ℂ _) SymmetricPowerLowDegree.oneEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u w
    change (a.exteriorPower n g u) ⊗ₜ[ℂ]
      SymmetricPowerLowDegree.evaluation (b.symmetricPower 1 g w) =
      (a.exteriorPower n g u) ⊗ₜ[ℂ] b g (SymmetricPowerLowDegree.evaluation w)
    have h := LinearMap.congr_fun
      ((SymmetricPowerLowDegree.representationOneEquiv b).isIntertwining' g) w
    exact congrArg ((a.exteriorPower n g u) ⊗ₜ[ℂ] ·) h

def pure (v : Fin n → A) (w : Fin m → B) :=
  exteriorPower.ιMulti ℂ n v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w

@[simp] theorem zeroBosonEquiv_pure (n : ℕ) (v : Fin n → A) (w : Fin 0 → B) :
    zeroBosonEquiv a b n (pure v w) = exteriorPower.ιMulti ℂ n v := by
  change SymmetricPowerLowDegree.zeroEvaluation (SymmetricPower.tprod ℂ w) •
    exteriorPower.ιMulti ℂ n v = _
  rw [SymmetricPowerLowDegree.zeroEvaluation_tprod, one_smul]

@[simp] theorem oneBosonEquiv_pure (n : ℕ) (v : Fin n → A) (w : Fin 1 → B) :
    oneBosonEquiv a b n (pure v w) = exteriorPower.ιMulti ℂ n v ⊗ₜ[ℂ] w 0 := by
  change exteriorPower.ιMulti ℂ n v ⊗ₜ[ℂ]
    SymmetricPowerLowDegree.evaluation (SymmetricPower.tprod ℂ w) = _
  rw [SymmetricPowerLowDegree.evaluation_tprod]

theorem ext {f h : Coefficient a b (n := n) (m := m)}
    (hp : ∀ v w, f (pure v w) = h (pure v w)) : f = h := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) B)
  rintro _ ⟨w, rfl⟩
  exact hp v w

theorem scalar_constraint (f : Coefficient a b (n := n) (m := m))
    (g : G) (v : Fin n → A) (w : Fin m → B)
    (c : Fin n → ℂ) (d : Fin m → ℂ)
    (hc : ∀ i, a g (v i) = c i • v i)
    (hd : ∀ j, b g (w j) = d j • w j) :
    ((∏ i, c i) * (∏ j, d j) - 1) * f (pure v w) = 0 := by
  have h := IntertwiningMap.isIntertwining _ _ f g (pure v w)
  simp only [pure, Representation.tprod_apply, TensorProduct.map_tmul,
    Representation.exteriorPower_apply_ιMulti,
    Representation.symmetricPower_apply_tprod, Function.comp_def, hc, hd,
    Representation.trivial_apply] at h
  have he := (exteriorPower.ιMulti ℂ n).toMultilinearMap.map_smul_univ c v
  change exteriorPower.ιMulti ℂ n (fun i => c i • v i) =
    (∏ i, c i) • exteriorPower.ιMulti ℂ n v at he
  have hs := (SymmetricPower.tprod ℂ).map_smul_univ d w
  rw [he, hs] at h
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_eq_mul] at h
  change (∏ j, d j) * ((∏ i, c i) * f (pure v w)) = f (pure v w) at h
  linear_combination h

theorem vanish_of_scalar (f : Coefficient a b (n := n) (m := m))
    (g : G) (v : Fin n → A) (w : Fin m → B)
    (c : Fin n → ℂ) (d : Fin m → ℂ)
    (hc : ∀ i, a g (v i) = c i • v i)
    (hd : ∀ j, b g (w j) = d j • w j)
    (hm : (∏ i, c i) * (∏ j, d j) ≠ 1) : f (pure v w) = 0 :=
  (mul_eq_zero.mp (scalar_constraint a b f g v w c d hc hd)).resolve_left
    (sub_ne_zero.mpr hm)

theorem circle_constraint (f : Coefficient a b (n := n) (m := m))
    (v : Fin n → A) (w : Fin m → B) (fw : Fin n → ℤ) (bw : Fin m → ℤ)
    (circle : Circle → G)
    (ha : ∀ z i, a (circle z) (v i) = (z : ℂ) ^ fw i • v i)
    (hb : ∀ z j, b (circle z) (w j) = (z : ℂ) ^ bw j • w j)
    (hf : f (pure v w) ≠ 0) : (∑ i, fw i) + (∑ j, bw j) = 0 := by
  apply ExteriorWeightSupport.circle_weight_zero
  intro z
  have h := scalar_constraint a b f (circle z) v w
    (fun i => (z : ℂ) ^ fw i) (fun j => (z : ℂ) ^ bw j) (ha z) (hb z)
  rw [ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero,
    ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero, ← zpow_add₀ z.coe_ne_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hf)

end
end Math.MixedWeightSupport
