import Math.RepresentationTheory.ExternalInvariantTensor
import Mathlib.RingTheory.TensorProduct.Finite

/-! Invariant tensor functionals as dual-valued intertwining maps. -/
namespace Math.InvariantTensorCurry
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct

variable {H A C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ H A) (c : Representation ℂ H C)

def curry (f : IntertwiningMap (a.tprod c) (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap a c.dual where
  toLinearMap := TensorProduct.curry f.toLinearMap
  isIntertwining' h := by
    ext x y
    change f (a h x ⊗ₜ[ℂ] y) = f (x ⊗ₜ[ℂ] c h⁻¹ y)
    have hi := IntertwiningMap.isIntertwining _ _ f h (x ⊗ₜ[ℂ] c h⁻¹ y)
    simpa [Representation.tprod_apply, ← Module.End.mul_apply, ← map_mul] using hi

def uncurry (f : IntertwiningMap a c.dual) :
    IntertwiningMap (a.tprod c) (Representation.trivial ℂ H ℂ) where
  toLinearMap := TensorProduct.lift f.toLinearMap
  isIntertwining' h := by
    ext x y
    change f (a h x) (c h y) = f x y
    rw [IntertwiningMap.isIntertwining _ _ f h x]
    change f x (c h⁻¹ (c h y)) = f x y
    simp [← Module.End.mul_apply, ← map_mul]

def equiv : IntertwiningMap (a.tprod c) (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ]
    IntertwiningMap a c.dual where
  toFun := curry a c
  invFun := uncurry a c
  left_inv f := by ext x y; rfl
  right_inv f := by ext x y; rfl
  map_add' f g := by ext x y; rfl
  map_smul' z f := by ext x y; rfl

def postcompose {N : Type*} [AddCommGroup N] [Module ℂ N]
    {n : Representation ℂ H N} (e : Representation.Equiv c n) :
    IntertwiningMap a c ≃ₗ[ℂ] IntertwiningMap a n where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by ext x; exact e.toLinearEquiv.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.toLinearEquiv.apply_symm_apply (f x)
  map_add' f g := by ext x; exact e.toLinearEquiv.map_add (f x) (g x)
  map_smul' z f := by ext x; exact e.toLinearEquiv.map_smul z (f x)

section TensorDual
variable {B D : Type*} [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
  (b : Representation ℂ H B) (d : Representation ℂ H D)

def tensorDual : Representation.Equiv (b.dual.tprod d.dual) (b.tprod d).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ B D
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro phi psi
    apply TensorProduct.ext'
    intro x y
    simp [Representation.tprod_apply, Representation.dual_apply, Module.Dual.transpose_apply]

def dualTensorDual : Representation.Equiv (b.dual.tprod d.dual).dual (b.tprod d) :=
  (dualEquiv (tensorDual b d)).trans (bidualEquiv (b.tprod d)).symm

def tensorValuedEquiv :
    IntertwiningMap (a.tprod (b.dual.tprod d.dual)) (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ]
      IntertwiningMap a (b.tprod d) :=
  (equiv a (b.dual.tprod d.dual)).trans
    (postcompose a (b.dual.tprod d.dual).dual (dualTensorDual b d))

end TensorDual
end
end Math.InvariantTensorCurry
