import Math.RepresentationTheory.Coefficients.InvariantCoefficientProduct

/-! Factorization of scalar permission for two independent group actions.
The factors here are the entire regrouped color/spin sources, not the
individual species before their color tensor products have been assembled. -/
namespace Math.ExternalCoefficientSupport
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor InvariantCoefficientTransport
open scoped TensorProduct
variable {G H A B : Type*} [Group G] [Group H]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ H B)

def leftSlice (f : Invariants (external a b)) (y : B) : Invariants a where
  toLinearMap := f.toLinearMap.comp ((TensorProduct.mk ℂ A B).flip y)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    simpa [external,Representation.tprod_apply] using f.isIntertwining _ _ (g,1) (x ⊗ₜ[ℂ] y)

def rightSlice (f : Invariants (external a b)) (x : A) : Invariants b where
  toLinearMap := f.toLinearMap.comp (TensorProduct.mk ℂ A B x)
  isIntertwining' g := by
    apply LinearMap.ext
    intro y
    simpa [external,Representation.tprod_apply] using f.isIntertwining _ _ (1,g) (x ⊗ₜ[ℂ] y)

/-- Independence of the group factors gives an exact iff only after all
species belonging to each group have been jointly assembled. -/
theorem allowed_iff : SelectionCriteria.Allowed (Invariants (external a b)) ↔
    SelectionCriteria.Allowed (Invariants a) ∧ SelectionCriteria.Allowed (Invariants b) := by
  constructor
  · rintro ⟨f,hf⟩
    have hp : ∃ x y, f (x ⊗ₜ[ℂ] y)≠0 := by
      by_contra! hp
      apply hf
      apply IntertwiningMap.ext
      apply TensorProduct.ext'
      intro x y
      exact hp x y
    obtain ⟨x,y,hxy⟩ := hp
    refine ⟨⟨leftSlice a b f y,?_⟩,⟨rightSlice a b f x,?_⟩⟩
    · intro hz
      exact hxy (DFunLike.congr_fun hz x)
    · intro hz
      exact hxy (DFunLike.congr_fun hz y)
  · rintro ⟨⟨f,hf⟩,⟨h,hh⟩⟩
    exact ⟨coefficient f h,coefficient_ne_zero f h hf hh⟩

end
end Math.ExternalCoefficientSupport
