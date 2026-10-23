import Math.RepresentationTheory.Constructions.TypedMixedSeparatedHom
import Math.RepresentationTheory.Relations.TypedMixedLocalHomNaturality
import Math.RepresentationTheory.Relations.LocalRelationTensorNaturality

/-! Generator evaluation for independently separated residual carriers. -/
namespace Math.TypedMixedSeparatedHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  {n m : ℕ} (p : Fin n → P) (s : Fin m → Q)

omit [Fintype P] [Fintype Q] in
theorem equiv_generator
    (q : MixedPatternAssembly.orderedSpace (fieldF a c) (fieldB b d) p s)
    (l : LocalCarrier (L := L) (K := K) p s)
    (v : MultiplicityCarrier (M := M) (N := N) p s) :
    equiv a b c d p s q
      ((LocalRelationTensorHom.relations (localOrdered a b p s)
        (multiplicityOrdered c d p s) (exchangeRelations c d p s)).mkQ
        ((LocalCoinvariantHom.relations (localOrdered a b p s)).mkQ l ⊗ₜ[ℂ] v)) =
      TypedMixedTensorHom.orderedEquiv.symm q.val
        (MixedTensorSeparation.equiv.symm (l ⊗ₜ[ℂ] v)) := by
  rfl
end
end Math.TypedMixedSeparatedHom
