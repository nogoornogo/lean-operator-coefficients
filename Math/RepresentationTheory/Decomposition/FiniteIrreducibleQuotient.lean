import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import Mathlib.RepresentationTheory.Maschke

/-!
# Actual irreducible quotients for finite residual groups

Maschke splitting supplies right inverses, including those needed to transport
contragredient fields. Constituents are selected from an actual decomposition.
-/

set_option autoImplicit false

namespace Math.FiniteIrreducibleQuotient

noncomputable section

open Representation FiniteSemisimpleDecomposition SplitRepresentationProjection
open scoped MonoidAlgebra

variable {H V W : Type*} [Group H] [Fintype H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_split (rho : Representation ℂ H V) (sigma : Representation ℂ H W)
    (p : IntertwiningMap rho sigma) (hp : Function.Surjective p) :
    ∃ S : Split rho sigma, S.project = p := by
  let : NeZero (Nat.card H : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  let f := IntertwiningMap.equivLinearMapAsModule rho sigma p
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f hp
    (LinearMap.id : sigma.asModule →ₗ[ℂ[H]] sigma.asModule)
  let e := (IntertwiningMap.equivLinearMapAsModule sigma rho).symm s
  refine ⟨⟨p, e, ?_⟩, rfl⟩
  intro x
  exact LinearMap.congr_fun hs x

variable {rho : Representation ℂ H V}

def blockProjection (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    IntertwiningMap rho (D.blockRepresentation i) where
  toLinearMap := (DFinsupp.lapply i).comp D.representationEquivDirectSum.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun x => x i)
      (IntertwiningMap.isIntertwining _ _
        D.representationEquivDirectSum.toIntertwiningMap g v)

omit [Fintype H] in
theorem blockProjection_surjective (D : Decomposition rho) (i : Fin D.numberOfBlocks) :
    Function.Surjective (blockProjection D i) := by
  classical
  intro x
  refine ⟨D.representationEquivDirectSum.symm (DFinsupp.single i x), ?_⟩
  change (D.representationEquivDirectSum
    (D.representationEquivDirectSum.symm (DFinsupp.single i x))) i = x
  simp

/-- A nonzero finite-dimensional representation has an actual irreducible
quotient carried by one of its invariant subspaces. -/
theorem exists_irreducible_quotient (rho : Representation ℂ H V)
    [FiniteDimensional ℂ V] [Nontrivial V] :
    ∃ S : Subrepresentation rho, IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∃ p : IntertwiningMap rho S.toRepresentation,
        Function.Surjective p := by
  classical
  let : NeZero (Nat.card H : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  obtain ⟨D⟩ := exists_decomposition rho inferInstance
  have hn : ∑ i, Module.finrank ℂ (D.block i) ≠ 0 := by
    rw [D.sum_finrank]
    exact ne_of_gt Module.finrank_pos
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  let S := D.subrepresentation i
  have hd : Module.finrank ℂ S.toSubmodule ≠ 0 := by
    rw [← (D.blockAmbientEquiv i).toLinearEquiv.finrank_eq]
    exact hi
  have ht : Nontrivial S.toSubmodule := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hd)
  refine ⟨S, D.subrepresentation_isIrreducible i, ht,
    (D.blockAmbientEquiv i).toIntertwiningMap.comp (blockProjection D i), ?_⟩
  exact (D.blockAmbientEquiv i).surjective.comp (blockProjection_surjective D i)

end
end Math.FiniteIrreducibleQuotient
