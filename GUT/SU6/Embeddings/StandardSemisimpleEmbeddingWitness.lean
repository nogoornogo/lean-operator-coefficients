import GUT.SU6.Hypercharge.StandardCentralGauge
import GUT.SU6.Embeddings.StandardSemisimpleEmbedding

/-!
# A complete semisimple embedding classification witness for the standard semisimple embedding

The standard block embedding `SU(3) x SU(2) -> SU(6)` has the concrete
one-parameter differential constructed in `StandardSemisimpleEmbedding`.
This file pairs it with the nontrivial central circle

`z |-> diag(z,z,z,z,z,z^(-5))`

and verifies the remaining commutation and nontriviality hypotheses of the semisimple embedding classification
classification endpoint.
-/

namespace GUT
namespace StandardSemisimpleEmbeddingWitness

noncomputable section

open CompactEmbeddingClassification

abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ

/-- The standard central gauge circle is literally diagonal in the ambient
six-dimensional basis. -/
theorem centralGauge_coe (z : Circle) :
    ((StandardCentralGauge.continuousHom z : SU6) : Matrix6) =
      Matrix.diagonal (StandardCentralGauge.coords z) := by
  have h := congrArg Subtype.val
    (StandardCentralGauge.diagonalPoint_toSU6_eq_hom z)
  change Matrix.diagonal (StandardCentralGauge.coords z) =
    ((StandardCentralGauge.continuousHom z : SU6) : Matrix6) at h
  exact h.symm

/-- The standard central gauge circle commutes with the standard semisimple
block embedding. -/
theorem centralGauge_commutes (z : Circle) (g : ProductGroup) :
    StandardCentralGauge.continuousHom z *
        StandardSemisimpleEmbedding.continuousEmbedding g =
      StandardSemisimpleEmbedding.continuousEmbedding g *
        StandardCentralGauge.continuousHom z := by
  apply Subtype.ext
  change
    ((StandardCentralGauge.continuousHom z : SU6) : Matrix6) *
        ((StandardSemisimpleEmbedding.embedding g : SU6) : Matrix6) =
      ((StandardSemisimpleEmbedding.embedding g : SU6) : Matrix6) *
        ((StandardCentralGauge.continuousHom z : SU6) : Matrix6)
  rw [centralGauge_coe, StandardSemisimpleEmbedding.embedding_coe]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [StandardCentralGauge.coords,
      StandardSemisimpleEmbedding.blockMatrix,
      StandardSemisimpleEmbedding.rawBlockMatrix,
      StandardSemisimpleEmbedding.singletMatrix,
      StandardSemisimpleEmbedding.rawSingletMatrix,
      ColorNeutralSMGroup.blockIndexEquiv_symm_zero,
      ColorNeutralSMGroup.blockIndexEquiv_symm_one,
      ColorNeutralSMGroup.blockIndexEquiv_symm_two,
      ColorNeutralSMGroup.blockIndexEquiv_symm_three,
      ColorNeutralSMGroup.blockIndexEquiv_symm_four,
      ColorNeutralSMGroup.blockIndexEquiv_symm_five, mul_comm]

/-- The central circle is not the trivial continuous homomorphism. -/
theorem centralGauge_ne_one :
    StandardCentralGauge.continuousHom ≠ 1 := by
  intro h
  have hz := DFunLike.congr_fun h (-1 : Circle)
  have hm := congrArg
    (fun U : SU6 => ((U : Matrix6) 0 0)) hz
  rw [centralGauge_coe] at hm
  norm_num [StandardCentralGauge.coords] at hm

/-- The standard embedding satisfies the classified semisimple embedding classification weak-doublet
decomposition endpoint with no extra source hypothesis. -/
theorem classifiedWeakDoubletDecomposition :
    Nonempty (WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction
        (StandardSemisimpleEmbedding.continuousEmbedding :
          ProductGroup →* SU6))) :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_oneParameterDifferentiableEmbedding
    StandardSemisimpleEmbedding.continuousEmbedding
    StandardSemisimpleEmbedding.embedding_injective
    StandardCentralGauge.continuousHom centralGauge_commutes
    centralGauge_ne_one
    StandardSemisimpleEmbedding.continuousOneParameterDifferentiable

/-- The numerical semisimple embedding classification branch classification for the same concrete standard
embedding. -/
theorem weakDoubletBranch :
    ∃ B : LowDimensionalIrreps.SixDimensionalBlockDecomposition,
      B.toBranchCounts.IsWeakDoubletBlock :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_oneParameterDifferentiableEmbedding
    StandardSemisimpleEmbedding.continuousEmbedding
    StandardSemisimpleEmbedding.embedding_injective
    StandardCentralGauge.continuousHom centralGauge_commutes
    centralGauge_ne_one
    StandardSemisimpleEmbedding.continuousOneParameterDifferentiable

end
end StandardSemisimpleEmbeddingWitness
end GUT
