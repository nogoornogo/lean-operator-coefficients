import Math.RepresentationTheory.FiniteInvariantFactor

/-! Exact change of local contraction dictionary, with arbitrary residual flavor.
Both dictionaries are independently normalized and exhaustive. -/
namespace Math.FiniteLocalBasisConversion
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantFactorization
open scoped TensorProduct
variable {G H A X I J : Type*} [Group G] [Group H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid X] [Module ℂ X]
  (a : Representation ℂ G A) (x : Representation ℂ H X)
  (p : I → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (v : I → A)
  (hv : ∀ i j, p i (v j) = if i = j then 1 else 0)
  (hp : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ i, f (v i) • p i)
  (q : J → IntertwiningMap a (Representation.trivial ℂ G ℂ)) (w : J → A)
  (hw : ∀ i j, q i (w j) = if i = j then 1 else 0)
  (hq : ∀ f : IntertwiningMap a (Representation.trivial ℂ G ℂ),
    f = ∑ j, f (w j) • q j)

/-- Change coordinates without changing the independently defined coefficient. -/
def equiv : (I → IntertwiningMap x (Representation.trivial ℂ H ℂ)) ≃ₗ[ℂ]
    (J → IntertwiningMap x (Representation.trivial ℂ H ℂ)) :=
  (FiniteInvariantFactor.equiv a x p v hv hp).symm.trans
    (FiniteInvariantFactor.equiv a x q w hw hq)

@[simp] theorem equiv_apply
    (c : I → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (j : J) (u : X) :
    equiv a x p v hv hp q w hw hq c j u = ∑ i, p i (w j) * c i u := by
  exact FiniteInvariantFactor.assemble_apply a x p c (w j) u

@[simp] theorem inverse_apply
    (c : J → IntertwiningMap x (Representation.trivial ℂ H ℂ)) (i : I) (u : X) :
    (equiv a x p v hv hp q w hw hq).symm c i u = ∑ j, q j (v i) * c j u := by
  exact FiniteInvariantFactor.assemble_apply a x q c (v i) u

theorem reconstruction_agrees
    (c : I → IntertwiningMap x (Representation.trivial ℂ H ℂ)) :
    FiniteInvariantFactor.assemble a x q (equiv a x p v hv hp q w hw hq c) =
      FiniteInvariantFactor.assemble a x p c := by
  exact (FiniteInvariantFactor.equiv a x q w hw hq).symm_apply_apply _

theorem inverse_left
    (c : I → IntertwiningMap x (Representation.trivial ℂ H ℂ)) :
    (equiv a x p v hv hp q w hw hq).symm
      (equiv a x p v hv hp q w hw hq c) = c :=
  (equiv a x p v hv hp q w hw hq).symm_apply_apply c

theorem inverse_right
    (c : J → IntertwiningMap x (Representation.trivial ℂ H ℂ)) :
    equiv a x p v hv hp q w hw hq
      ((equiv a x p v hv hp q w hw hq).symm c) = c :=
  (equiv a x p v hv hp q w hw hq).apply_symm_apply c

end
end Math.FiniteLocalBasisConversion
