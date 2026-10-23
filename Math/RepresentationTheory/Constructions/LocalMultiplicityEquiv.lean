import Math.RepresentationTheory.Tensors.MixedTensorSeparation
import Math.RepresentationTheory.Relations.LocalCoinvariantTensor

/-! Factorized presentation changes supply the paired-field interface without
additional assumptions. -/
namespace Math.LocalMultiplicityEquiv
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G H L M L' M' : Type*} [Group G] [Group H]
  [AddCommGroup L] [Module ℂ L] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup L'] [Module ℂ L'] [AddCommGroup M'] [Module ℂ M']
  (a : Representation ℂ G L) (b : Representation ℂ H M)
  (a' : Representation ℂ G L') (b' : Representation ℂ H M')
  (e : Representation.Equiv a a') (f : Representation.Equiv b b')

def trivialEquiv (h : L ≃ₗ[ℂ] L') : Representation.Equiv (trivial ℂ H L) (trivial ℂ H L') where
  toLinearEquiv := h
  isIntertwining' _ := by ext u; rfl

def paired : Representation.Equiv (LocalCoinvariantTensor.residual (L := L) b)
    (LocalCoinvariantTensor.residual (L := L') b') :=
  MixedTensorSeparation.tensorCongr (trivialEquiv (H := H) e.toLinearEquiv) f

theorem local_compatible (g : G) (u : L ⊗[ℂ] M) :
    paired a b a' b' e f (LocalCoinvariantTensor.action (M := M) a g u) =
    LocalCoinvariantTensor.action (M := M') a' g (paired a b a' b' e f u) := by
  have he : (paired a b a' b' e f).toLinearMap.comp
      (LocalCoinvariantTensor.action (M := M) a g) =
      (LocalCoinvariantTensor.action (M := M') a' g).comp
        (paired a b a' b' e f).toLinearMap := by
    apply TensorProduct.ext'
    intro l m
    change e (a g l) ⊗ₜ[ℂ] f m = a' g (e l) ⊗ₜ[ℂ] f m
    exact congrArg (fun v => v ⊗ₜ[ℂ] f m)
      (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g l)
  exact LinearMap.congr_fun he u
end
end Math.LocalMultiplicityEquiv
