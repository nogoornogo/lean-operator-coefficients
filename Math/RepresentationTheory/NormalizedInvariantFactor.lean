import Math.RepresentationTheory.ExternalInvariantFactorization

/-! Extract a normalized, exhaustive local invariant factor. -/
namespace Math.NormalizedInvariantFactor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct

variable {K H T X : Type*} [Group K] [Group H]
  [AddCommMonoid T] [Module ℂ T] [AddCommMonoid X] [Module ℂ X]
  (t : Representation ℂ K T) (x : Representation ℂ H X)
  (p : IntertwiningMap t (Representation.trivial ℂ K ℂ)) (v : T)
  (hv : p v = 1)
  (hp : ∀ k : IntertwiningMap t (Representation.trivial ℂ K ℂ), k = k v • p)

/-- The domain contains all invariants, not only assembled coefficients. -/
def equiv : Coefficient t x ≃ₗ[ℂ]
    IntertwiningMap x (Representation.trivial ℂ H ℂ) where
  toFun f := rightSlice t x f v
  invFun f := coefficient p f
  left_inv f := (factor_left t x p v hp f).symm
  right_inv f := by ext w; simp [rightSlice, hv]
  map_add' f g := by ext w; rfl
  map_smul' z f := by ext w; rfl

@[simp] theorem equiv_apply_tmul (f : Coefficient t x) (w : X) :
    equiv t x p v hv hp f w = f (v ⊗ₜ[ℂ] w) := rfl

theorem reconstruction (f : Coefficient t x) (u : T) (w : X) :
    f (u ⊗ₜ[ℂ] w) = p u * equiv t x p v hv hp f w := by
  exact DFunLike.congr_fun (factor_left t x p v hp f) (u ⊗ₜ[ℂ] w)

include p v hv hp in
theorem exists_nonzero_iff :
    (∃ f : Coefficient t x, f ≠ 0) ↔
      ∃ r : IntertwiningMap x (Representation.trivial ℂ H ℂ), r ≠ 0 := by
  let e := equiv t x p v hv hp
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨e f, fun h => hf (e.injective (h.trans e.map_zero.symm))⟩
  · rintro ⟨r, hr⟩
    exact ⟨e.symm r, fun h => hr (e.symm.injective (h.trans e.symm.map_zero.symm))⟩

end

section Product
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A B : Type*} [Group G] [Group H]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ H B)
  (p : IntertwiningMap a (Representation.trivial ℂ G ℂ))
  (q : IntertwiningMap b (Representation.trivial ℂ H ℂ)) (v : A) (w : B)

theorem product_unique
    (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = k v • p)
    (hq : ∀ k : IntertwiningMap b (Representation.trivial ℂ H ℂ), k = k w • q)
    (f : Coefficient a b) : f = f (v ⊗ₜ[ℂ] w) • coefficient p q := by
  have h := factor_left a b p v hp f
  rw [hq (rightSlice a b f v)] at h
  calc
    f = coefficient p (f (v ⊗ₜ[ℂ] w) • q) := h
    _ = f (v ⊗ₜ[ℂ] w) • coefficient p q := by
      ext x y
      change p x * (f (v ⊗ₜ[ℂ] w) * q y) = f (v ⊗ₜ[ℂ] w) * (p x * q y)
      ring

end Product
end Math.NormalizedInvariantFactor
