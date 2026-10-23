import Math.RepresentationTheory.Exterior.ExteriorWeightSupport
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Full-circle scalar action detects the charge of a tensor coefficient. -/
namespace Math.InvariantTensorCharge
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]
  (a : Representation ℂ G X) (b : Representation ℂ G Y)

theorem charge_zero (circle : Circle → G) (w t : ℤ)
    (ha : ∀ z x, a (circle z) x = (z : ℂ)^w • x)
    (hb : ∀ z y, b (circle z) y = (z : ℂ)^t • y)
    (ht : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b))) :
    w+t=0 := by
  obtain ⟨f,hf⟩ := ht
  by_contra hn
  apply hf
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change f (x ⊗ₜ[ℂ] y) = 0
  by_contra hv
  apply hn
  apply ExteriorWeightSupport.circle_weight_zero
  intro z
  have he := f.isIntertwining _ _ (circle z) (x ⊗ₜ[ℂ] y)
  change f (a (circle z) x ⊗ₜ[ℂ] b (circle z) y) = f (x ⊗ₜ[ℂ] y) at he
  rw [ha,hb,TensorProduct.smul_tmul_smul,map_smul,smul_eq_mul,
    ← zpow_add₀ z.coe_ne_zero] at he
  exact mul_right_cancel₀ hv (he.trans (one_mul _).symm)

end
end Math.InvariantTensorCharge
