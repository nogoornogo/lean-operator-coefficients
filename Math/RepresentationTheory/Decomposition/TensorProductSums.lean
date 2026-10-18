import Math.RepresentationTheory.ExternalInvariantTensor
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! Equivariant distribution and rearrangement of finite product summands.
These maps preserve the diagonal group action on every entire source. -/
namespace Math.TensorProductSums
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
variable {G A B C D E F : Type*} [Group G]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  [AddCommMonoid C] [Module ℂ C] [AddCommMonoid D] [Module ℂ D]
  [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
  (a : Representation ℂ G A) (b : Representation ℂ G B)
  (c : Representation ℂ G C) (d : Representation ℂ G D)
  (e : Representation ℂ G E) (f : Representation ℂ G F)

def prodComm : Representation.Equiv (a.prod b) (b.prod a) where
  toLinearEquiv := LinearEquiv.prodComm ℂ A B
  isIntertwining' _ := by ext x <;> rfl

def prodLeft : Representation.Equiv ((a.prod b).tprod c) ((a.tprod c).prod (b.tprod c)) where
  toLinearEquiv := TensorProduct.prodLeft ℂ ℂ A B C
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    apply Prod.ext <;> rfl

def prodRight : Representation.Equiv (a.tprod (b.prod c)) ((a.tprod b).prod (a.tprod c)) where
  toLinearEquiv := TensorProduct.prodRight ℂ ℂ A B C
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    apply Prod.ext <;> rfl

def expand : Representation.Equiv ((a.prod b).tprod (c.prod d))
    (((a.tprod c).prod (a.tprod d)).prod ((b.tprod c).prod (b.tprod d))) :=
  (prodLeft a b (c.prod d)).trans
    (SplitRepresentationProjection.prodEquiv (prodRight a c d) (prodRight b c d))

/-- Move the first and fourth of six actual summands to a common last block. -/
def sixReorder : Representation.Equiv (((a.prod b).prod (c.prod d)).prod (e.prod f))
    (((b.prod c).prod (e.prod f)).prod (a.prod d)) where
  toLinearEquiv :=
    { toFun x := (((x.1.1.2,x.1.2.1),x.2),(x.1.1.1,x.1.2.2))
      invFun x := (((x.2.1,x.1.1.1),(x.1.1.2,x.2.2)),x.1.2)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := by ext x <;> rfl

end
end Math.TensorProductSums
