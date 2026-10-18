import GUT.SU6.Embeddings.ActualBlockChoiceIndependence
import GUT.SU6.Embeddings.StandardSemisimpleEmbeddingWitness
import GUT.SU6.SelectionRules.FinalNoGoAssembly

/-!
# Concrete continuity-only geometry with the standard hypercharge pair

The block embedding and its semisimple embedding classification certificate are constructed independently of
the matter spectrum. Independence of the block choice identifies the pair
extracted by the final-theorem interface without assuming its value.
-/

namespace GUT.ConcreteStandardGeometry

open CompactEmbeddingClassification ActualCompactCentralizer ActualBlockCentralizer
open FinalNoGoAssembly

noncomputable section
set_option autoImplicit false

def blocks : WeakDoubletData
    (euclideanDefiningRestriction StandardSemisimpleEmbedding.embedding) :=
  Classical.choice StandardSemisimpleEmbeddingWitness.classifiedWeakDoubletDecomposition

def centralizerVal : PhysicalCentralizer StandardSemisimpleEmbedding.embedding →ₜ* SU6 where
  toMonoidHom := (PhysicalCentralizer StandardSemisimpleEmbedding.embedding).subtype
  continuous_toFun := continuous_subtype_val

def hypercharge : Circle →ₜ* SU6 :=
  centralizerVal.comp
    (physicalCircleHom StandardSemisimpleEmbedding.embedding blocks (-2, 3))

theorem hypercharge_injective : Function.Injective hypercharge := by
  have h := (physicalCircleHom_injective_iff
    StandardSemisimpleEmbedding.embedding blocks (-2, 3)).mpr (by norm_num)
  intro z w hzw
  apply h
  exact Subtype.ext hzw

def geometry : ContinuousHyperchargeEmbedding where
  iota := StandardSemisimpleEmbedding.continuousEmbedding
  embedding_injective := StandardSemisimpleEmbedding.embedding_injective
  hypercharge := hypercharge
  hypercharge_injective := hypercharge_injective
  hypercharge_commutes := by
    intro z g
    have h := (physicalCircleHom StandardSemisimpleEmbedding.embedding blocks (-2, 3) z).property
    rw [Subgroup.mem_centralizer_iff] at h
    exact (h _ ⟨g, rfl⟩).symm

theorem hyperchargePair_eq_standard :
    geometry.hyperchargePair = (-2, 3) := by
  apply (integerPairEquivPhysicalCircleHom
    StandardSemisimpleEmbedding.embedding geometry.weakDoubletData).injective
  change physicalCircleHom _ _ geometry.hyperchargePair = physicalCircleHom _ _ (-2, 3)
  refine geometry.toMatrixDifferentiable.centralizerCircle_eq_physicalCircleHom.symm.trans ?_
  apply ContinuousMonoidHom.ext
  intro z
  apply Subtype.ext
  change (physicalCircleHom StandardSemisimpleEmbedding.embedding blocks (-2, 3) z : SU6) = _
  exact congrArg Subtype.val (DFunLike.congr_fun
    (ActualBlockChoiceIndependence.physicalCircleHom_independent
      StandardSemisimpleEmbedding.embedding blocks geometry.weakDoubletData (-2, 3)) z)

end
end GUT.ConcreteStandardGeometry
