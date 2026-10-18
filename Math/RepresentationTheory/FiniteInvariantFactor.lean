import Math.RepresentationTheory.ExternalInvariantFactorization

/-! An exhaustive finite local invariant basis with dual probes factors out of
an external invariant coefficient. No finite-dimensionality of flavor is needed. -/
namespace Math.FiniteInvariantFactor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X ι : Type*} [Group G] [Group H] [Fintype ι] [DecidableEq ι]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : ι → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : ι → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = ∑ i, k (v i) • p i)

def assemble (c : ι → IntertwiningMap x (Representation.trivial ℂ H ℂ)) : Coefficient a x :=
  ∑ i, coefficient (p i) (c i)

omit [DecidableEq ι] in
theorem assemble_apply (c : ι → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (u : A) (w : X) :
    assemble a x p c (u ⊗ₜ[ℂ] w) = ∑ i, p i u * c i w := by
  simp [assemble, IntertwiningMap.sum_apply, coefficient]

include hp in
omit [DecidableEq ι] in
theorem reconstruction (f : Coefficient a x) :
    f = assemble a x p (fun i => rightSlice a x f (v i)) := by
  ext u w
  have h := DFunLike.congr_fun (hp (leftSlice a x f w)) u
  simpa [assemble_apply, IntertwiningMap.sum_apply, leftSlice, rightSlice, mul_comm] using h

include hv in
theorem probe_assemble (c : ι → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (j : ι) :
    rightSlice a x (assemble a x p c) (v j) = c j := by
  ext w
  change assemble a x p c (v j ⊗ₜ[ℂ] w) = c j w
  simp [assemble_apply, hv]

def equiv : Coefficient a x ≃ₗ[ℂ] (ι → IntertwiningMap x (Representation.trivial ℂ H ℂ)) where
  toFun f i := rightSlice a x f (v i)
  invFun := assemble a x p
  left_inv f := (reconstruction a x p v hp f).symm
  right_inv c := funext (probe_assemble a x p v hv c)
  map_add' f g := by funext i; ext w; rfl
  map_smul' z f := by funext i; ext w; rfl

end

section Product
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X ι : Type*} [Group G] [Group H] [Fintype ι]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : A)
  (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = k v • p)
  (q : ι → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (w : ι → X)
  (hq : ∀ k : IntertwiningMap x (Representation.trivial ℂ H ℂ), k = ∑ i, k (w i) • q i)

include hp hq in
theorem product_left_line (f : Coefficient a x) :
    f = ∑ i, f (v ⊗ₜ[ℂ] w i) • coefficient p (q i) := by
  have h := factor_left a x p v hp f
  rw [hq (rightSlice a x f v)] at h
  calc
    f = coefficient p (∑ i, (rightSlice a x f v) (w i) • q i) := h
    _ = _ := by
      ext u z
      simp [coefficient, IntertwiningMap.sum_apply, rightSlice, Finset.mul_sum, mul_assoc, mul_comm]

end
end Product

section FiniteProduct
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X ι κ : Type*} [Group G] [Group H] [Fintype ι] [Fintype κ]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : ι → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : ι → A)
  (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = ∑ i, k (v i) • p i)
  (q : κ → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (w : κ → X)
  (hq : ∀ k : IntertwiningMap x (Representation.trivial ℂ H ℂ), k = ∑ j, k (w j) • q j)

include hp hq in
/-- Products of exhaustive finite local families exhaust the external product. -/
theorem product_formula (f : Coefficient a x) :
    f = ∑ ij : ι × κ, f (v ij.1 ⊗ₜ[ℂ] w ij.2) • coefficient (p ij.1) (q ij.2) := by
  classical
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro u z
  have hl := DFunLike.congr_fun (hp (leftSlice a x f z)) u
  have hr (i : ι) := DFunLike.congr_fun (hq (rightSlice a x f (v i))) z
  change f (u ⊗ₜ[ℂ] z) =
    (∑ ij : ι × κ, f (v ij.1 ⊗ₜ[ℂ] w ij.2) • coefficient (p ij.1) (q ij.2)) (u ⊗ₜ[ℂ] z)
  simp only [IntertwiningMap.sum_apply] at hl hr ⊢
  change f (u ⊗ₜ[ℂ] z) = ∑ ij : ι × κ, f (v ij.1 ⊗ₜ[ℂ] w ij.2) *
    (p ij.1 u * q ij.2 z)
  change f (u ⊗ₜ[ℂ] z) = ∑ i, f (v i ⊗ₜ[ℂ] z) * p i u at hl
  rw [hl, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hr i
  change f (v i ⊗ₜ[ℂ] z) = ∑ j, f (v i ⊗ₜ[ℂ] w j) * q j z at hi
  rw [hi, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end FiniteProduct

section RightLine
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X ι : Type*} [Group G] [Group H] [Fintype ι]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : ι → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : ι → A)
  (hp : ∀ k : IntertwiningMap a (Representation.trivial ℂ G ℂ), k = ∑ i, k (v i) • p i)
  (q : IntertwiningMap x (Representation.trivial ℂ H ℂ)) (w : X)
  (hq : ∀ k : IntertwiningMap x (Representation.trivial ℂ H ℂ), k = k w • q)

include hp hq in
theorem product_right_line (f : Coefficient a x) :
    f = ∑ i, f (v i ⊗ₜ[ℂ] w) • coefficient (p i) q := by
  have h := factor_right a x q w hq f
  rw [hp (leftSlice a x f w)] at h
  calc
    f = coefficient (∑ i, (leftSlice a x f w) (v i) • p i) q := h
    _ = _ := by
      ext u z
      simp [coefficient, IntertwiningMap.sum_apply, leftSlice, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm]

end
end RightLine
end Math.FiniteInvariantFactor
