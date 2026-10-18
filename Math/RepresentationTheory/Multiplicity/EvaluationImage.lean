import Math.RepresentationTheory.Decomposition.ProductFactorization
import Math.RepresentationTheory.Decomposition.SemisimpleSplitting

/-! Canonical multiplicity models as actual invariant subspaces. Neither the
ambient representation nor the multiplicity representation must be irreducible.
The dual image is obtained from a derived retraction, not an extra input. -/

namespace Math.MultiplicityEvaluationImage
noncomputable section
open Representation ProductFactorization ExternalTensorProduct SplitRepresentationProjection
open scoped TensorProduct

variable {G H U V : Type*} [Group G] [Group H]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  [AddCommGroup V] [Module ℂ V]
  (tau : Representation ℂ (G × H) V) (r : Representation ℂ G U)

abbrev model := externalTprod r (multiplicityRepresentation tau r)

def image : Subrepresentation tau := (multiplicityEvaluation tau r).range

omit [FiniteDimensional ℂ U] in
/-- The evaluation image contains all copies, not just one selected embedding. -/
theorem image_le_iff (S : Subrepresentation tau) :
    image tau r ≤ S ↔ ∀ (f : MultiplicitySpace tau r) (x : U), f x ∈ S := by
  constructor
  · intro h f x
    exact h ⟨x ⊗ₜ[ℂ] f, rfl⟩
  · intro h v hv
    obtain ⟨z, rfl⟩ := hv
    change multiplicityEvaluation tau r z ∈ S.toSubmodule
    induction z using TensorProduct.inductionOn with
    | tmul x f => exact h f x
    | add x y hx hy => simpa using S.toSubmodule.add_mem hx hy

def toImage : IntertwiningMap (model tau r) (image tau r).toRepresentation where
  toLinearMap := (multiplicityEvaluation tau r).toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact IntertwiningMap.isIntertwining _ _ (multiplicityEvaluation tau r) g x

omit [FiniteDimensional ℂ U] in
@[simp] theorem toImage_tmul (u : U) (f : MultiplicitySpace tau r) :
    (toImage tau r (u ⊗ₜ[ℂ] f) : V) = f u := rfl

omit [FiniteDimensional ℂ U] in
theorem toImage_surjective : Function.Surjective (toImage tau r) := by
  rintro ⟨x, y, hy⟩
  exact ⟨y, Subtype.ext hy⟩

variable [IsIrreducible r]

def equiv : Representation.Equiv (model tau r) (image tau r).toRepresentation :=
  IntertwiningMap.ofBijective (toImage tau r)
    ⟨fun _ _ h => multiplicityEvaluationLinear_injective tau r (congrArg Subtype.val h),
      toImage_surjective tau r⟩

@[simp] theorem equiv_tmul (u : U) (f : MultiplicitySpace tau r) :
    (equiv tau r (u ⊗ₜ[ℂ] f) : V) = f u := rfl

theorem exists_split (ht : IsSemisimpleRepresentation tau) :
    ∃ S : Split tau (model tau r), S.embed = multiplicityEvaluation tau r :=
  SemisimpleSplitting.exists_retraction tau (model tau r) ht
    (multiplicityEvaluation tau r) (multiplicityEvaluationLinear_injective tau r)

/-- Dualizing the derived projection embeds the full dual multiplicity model
in the actual algebraic dual, and restriction to evaluation is its left inverse. -/
theorem exists_dual_embedding (ht : IsSemisimpleRepresentation tau) :
    ∃ i : IntertwiningMap (model tau r).dual tau.dual,
      Function.Injective i ∧ ∀ phi x, i phi (multiplicityEvaluation tau r x) = phi x := by
  obtain ⟨S, hs⟩ := exists_split tau r ht
  refine ⟨S.dual.embed, ?_, ?_⟩
  · exact Function.LeftInverse.injective S.dual.left_inv
  · intro phi x
    change phi (S.project (multiplicityEvaluation tau r x)) = phi x
    rw [← hs, S.left_inv]

/-- Both the subspace and the equivalence on the dual side are constructed. -/
theorem exists_dual_image (ht : IsSemisimpleRepresentation tau) :
    ∃ S : Subrepresentation tau.dual,
      Nonempty (Representation.Equiv (model tau r).dual S.toRepresentation) := by
  obtain ⟨i, hi, _⟩ := exists_dual_embedding tau r ht
  let q : IntertwiningMap (model tau r).dual i.range.toRepresentation :=
    { toLinearMap := i.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact IntertwiningMap.isIntertwining _ _ i g x }
  refine ⟨i.range, ⟨IntertwiningMap.ofBijective q ⟨?_, ?_⟩⟩⟩
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · rintro ⟨x, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

end
end Math.MultiplicityEvaluationImage
