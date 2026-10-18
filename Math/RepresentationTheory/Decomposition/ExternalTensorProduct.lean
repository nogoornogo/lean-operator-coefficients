import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic

/-!
# External tensor products of representations

Mathlib's `Representation.tprod` tensors two representations of the same
group, using the diagonal action.  For the `SU(3) x SU(2)` classification we
also need the external tensor product: the first factor acts on the first
space and the second factor acts on the second space.
-/

namespace Math
namespace ExternalTensorProduct

noncomputable section

open TensorProduct

variable {k G H V W : Type*}
variable [CommSemiring k] [Monoid G] [Monoid H]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]

/-- The external tensor product of a `G`-representation and an
`H`-representation, as a representation of `G × H`. -/
def externalTprod (rho : Representation k G V) (sigma : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) where
  toFun gh := TensorProduct.map (rho gh.1) (sigma gh.2)
  map_one' := by
    change TensorProduct.map (rho 1) (sigma 1) = 1
    rw [map_one, map_one]
    exact TensorProduct.map_one
  map_mul' g h := by
    change
      TensorProduct.map (rho (g.1 * h.1)) (sigma (g.2 * h.2)) =
        TensorProduct.map (rho g.1) (sigma g.2) *
          TensorProduct.map (rho h.1) (sigma h.2)
    rw [map_mul, map_mul]
    exact TensorProduct.map_mul _ _ _ _

@[simp]
theorem externalTprod_apply
    (rho : Representation k G V) (sigma : Representation k H W) (g : G) (h : H) :
    externalTprod rho sigma (g, h) = TensorProduct.map (rho g) (sigma h) :=
  rfl

@[simp]
theorem externalTprod_tmul
    (rho : Representation k G V) (sigma : Representation k H W)
    (g : G) (h : H) (v : V) (w : W) :
    externalTprod rho sigma (g, h) (v ⊗ₜ[k] w) = rho g v ⊗ₜ[k] sigma h w := by
  simp [externalTprod]

@[simp]
theorem externalTprod_fst_tmul
    (rho : Representation k G V) (sigma : Representation k H W)
    (g : G) (v : V) (w : W) :
    externalTprod rho sigma (g, 1) (v ⊗ₜ[k] w) = rho g v ⊗ₜ[k] w := by
  simp

@[simp]
theorem externalTprod_snd_tmul
    (rho : Representation k G V) (sigma : Representation k H W)
    (h : H) (v : V) (w : W) :
    externalTprod rho sigma (1, h) (v ⊗ₜ[k] w) = v ⊗ₜ[k] sigma h w := by
  simp

/-- Scalar actions on the two factors multiply on the external tensor
product.  This is the center-character calculation used for product blocks. -/
theorem externalTprod_apply_eq_smul_id
    (rho : Representation k G V) (sigma : Representation k H W)
    (g : G) (h : H) (a b : k)
    (hg : rho g = a • (LinearMap.id : V →ₗ[k] V))
    (hh : sigma h = b • (LinearMap.id : W →ₗ[k] W)) :
    externalTprod rho sigma (g, h) =
      (a * b) • (LinearMap.id : (V ⊗[k] W) →ₗ[k] (V ⊗[k] W)) := by
  apply TensorProduct.ext'
  intro v w
  simp only [externalTprod_apply, hg, hh, TensorProduct.map_tmul,
    LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul]
  rw [smul_smul, mul_comm]

end

end ExternalTensorProduct
end Math
