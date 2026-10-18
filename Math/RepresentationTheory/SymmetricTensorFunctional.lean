import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.TensorSquareMultilinear

/-! Symmetry in the first tensor pair, without dual-flavor identifications. -/
namespace Math.SymmetricTensorFunctional
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H A C : Type*} [Group H] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ H A) (c : Representation ℂ H C)

abbrev Functionals := IntertwiningMap ((a.tprod a).tprod c) (trivial ℂ H ℂ)
def symmetric : Submodule ℂ (Functionals a c) where
  carrier := {f | ∀ x y z, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] z) = f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)}
  zero_mem' := by intro x y z; rfl
  add_mem' := by intro f g hf hg x y z; change f _+g _=f _+g _; rw [hf,hg]
  smul_mem' := by intro t f hf x y z; change t • f _=t • f _; rw [hf]

def curryEquiv : symmetric a c ≃ₗ[ℂ]
    TensorSquareMultilinear.symmetricIntertwiners a c.dual where
  toFun f := ⟨InvariantTensorCurry.equiv (a.tprod a) c f.val, by
    intro x y; ext z; exact f.property x y z⟩
  invFun f := ⟨(InvariantTensorCurry.equiv (a.tprod a) c).symm f.val, by
    intro x y z; exact DFunLike.congr_fun (f.property x y) z⟩
  left_inv f := by apply Subtype.ext; exact (InvariantTensorCurry.equiv _ _).symm_apply_apply _
  right_inv f := by apply Subtype.ext; exact (InvariantTensorCurry.equiv _ _).apply_symm_apply _
  map_add' f g := by apply Subtype.ext; exact (InvariantTensorCurry.equiv _ _).map_add _ _
  map_smul' t f := by apply Subtype.ext; exact (InvariantTensorCurry.equiv _ _).map_smul _ _

def equiv : symmetric a c ≃ₗ[ℂ]
    IntertwiningMap ((a.symmetricPower 2).tprod c) (trivial ℂ H ℂ) :=
  (curryEquiv a c).trans ((TensorSquareMultilinear.symmetricSquareEquiv a c.dual).trans
    (InvariantTensorCurry.equiv (a.symmetricPower 2) c).symm)

end
end Math.SymmetricTensorFunctional
