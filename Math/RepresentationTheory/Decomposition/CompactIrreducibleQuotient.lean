import Math.RepresentationTheory.Unitary.FiniteBasisUnitaryModel
import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Decomposition.FiniteIrreducibleQuotient
import Math.RepresentationTheory.Decomposition.SemisimpleSplitting

/-! Compact continuous representations: complete reducibility and actual
irreducible quotients on the original carrier, without assuming H-unitarity. -/

namespace Math.CompactIrreducibleQuotient
noncomputable section

open Representation ContinuousRepresentationScope FiniteSemisimpleDecomposition
open scoped MonoidAlgebra

variable {H V : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem semisimple (rho : Representation ℂ H V) (hr : IsJointlyContinuous rho) :
    IsSemisimpleRepresentation rho := by
  let b := Module.finBasis ℂ V
  have hc : ∀ i j, Continuous fun h => b.coord i (rho h (b j)) := fun i j =>
    (b.coord i).continuous_of_finiteDimensional.comp (hr.orbit (b j))
  let sigma := (FiniteBasisUnitaryModel.model b rho hc).toRepresentation
  have hs : IsSemisimpleRepresentation sigma :=
    UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary sigma
      (FiniteBasisUnitaryModel.model_inner b rho hc)
  let e := FiniteBasisUnitaryModel.modelEquiv b rho hc
  let f := IntertwiningMap.equivLinearMapAsModule rho sigma e.toIntertwiningMap
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hs ⊢
  exact (f.isSemisimpleModule_iff_of_bijective e.bijective).mpr hs

theorem exists_irreducible_quotient (rho : Representation ℂ H V)
    (hr : IsJointlyContinuous rho) [Nontrivial V] :
    ∃ S : Subrepresentation rho, IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∃ p : IntertwiningMap rho S.toRepresentation,
        Function.Surjective p := by
  classical
  obtain ⟨D⟩ := exists_decomposition rho (semisimple rho hr)
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
    (D.blockAmbientEquiv i).toIntertwiningMap.comp
      (FiniteIrreducibleQuotient.blockProjection D i), ?_⟩
  exact (D.blockAmbientEquiv i).surjective.comp
    (FiniteIrreducibleQuotient.blockProjection_surjective D i)

end
end Math.CompactIrreducibleQuotient
