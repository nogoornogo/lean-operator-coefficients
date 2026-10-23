import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

/-! Factor an external invariant when one factor has a unique invariant contraction. -/
namespace Math.ExternalInvariantFactorization
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct

variable {G H A X : Type*} [Group G] [Group H]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)

abbrev Coefficient := IntertwiningMap (external a x) (Representation.trivial ℂ (G × H) ℂ)

def rightSlice (f : Coefficient a x) (v : A) :
    IntertwiningMap x (Representation.trivial ℂ H ℂ) where
  toLinearMap := f.toLinearMap.comp (TensorProduct.mk ℂ A X v)
  isIntertwining' h := by
    ext w
    have hi := IntertwiningMap.isIntertwining _ _ f (1, h) (v ⊗ₜ[ℂ] w)
    simpa [external] using hi

def leftSlice (f : Coefficient a x) (w : X) :
    IntertwiningMap a (Representation.trivial ℂ G ℂ) where
  toLinearMap := f.toLinearMap.comp ((TensorProduct.mk ℂ A X).flip w)
  isIntertwining' g := by
    ext v
    have hi := IntertwiningMap.isIntertwining _ _ f (g, 1) (v ⊗ₜ[ℂ] w)
    simpa [external] using hi

theorem factor_right (p : IntertwiningMap x (Representation.trivial ℂ H ℂ)) (w : X)
    (hp : ∀ k : IntertwiningMap x (Representation.trivial ℂ H ℂ), k = k w • p)
    (f : Coefficient a x) : f = coefficient (leftSlice a x f w) p := by
  ext v z
  have h := DFunLike.congr_fun (hp (rightSlice a x f v)) z
  exact h

theorem factor_left (p : IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : A)
    (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = k v • p)
    (f : Coefficient a x) : f = coefficient p (rightSlice a x f v) := by
  ext w z
  have h := DFunLike.congr_fun (hp (leftSlice a x f z)) w
  change f (w ⊗ₜ[ℂ] z) = f (v ⊗ₜ[ℂ] z) * p w at h
  change f (w ⊗ₜ[ℂ] z) = p w * f (v ⊗ₜ[ℂ] z)
  exact h.trans (mul_comm _ _)

end
end Math.ExternalInvariantFactorization
