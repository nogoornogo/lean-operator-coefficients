import GUT.SU6.Embeddings.SmoothEmbeddingBridge
import GUT.SU6.Embeddings.StandardSemisimpleEmbedding

/-!
# Smooth source witness for the standard semisimple embedding

The standard block embedding is the restriction of an affine map on the two
ambient matrix spaces.  This file verifies the new ordinary differentiability
source condition and therefore demonstrates that the smooth semisimple embedding classification bridge is
inhabited by the intended representative.
-/

namespace GUT
namespace StandardSmoothEmbeddingWitness

noncomputable section

open CompactEmbeddingClassification
open SmoothEmbeddingBridge
open scoped Matrix.Norms.L2Operator

/-- The affine ambient extension of the standard block embedding. -/
def ambientExtension (AB : SourceMatrix) :
    EmbeddingDifferentialBridge.Matrix6 :=
  StandardSemisimpleEmbedding.blockMatrix AB +
    StandardSemisimpleEmbedding.singletMatrix

set_option backward.isDefEq.respectTransparency false in
/-- The standard block embedding is ambiently differentiable at the identity. -/
def ambientlyDifferentiable :
    AmbientlyDifferentiableEmbedding
      StandardSemisimpleEmbedding.embedding where
  extension := ambientExtension
  agrees_on_group := by
    intro g
    simpa [ambientExtension] using
      (StandardSemisimpleEmbedding.embedding_coe g).symm
  differentiableAt_identity := by
    change DifferentiableAt ℝ
      (fun AB : SourceMatrix =>
        StandardSemisimpleEmbedding.blockMatrixContinuousLinear AB +
          StandardSemisimpleEmbedding.singletMatrix) 1
    fun_prop

/-- In particular, the standard representative is differentiable at zero in
the source exponential coordinates used by the general semisimple embedding classification theorem. -/
theorem exponentialChart_differentiableAt :
    DifferentiableAt ℝ
      (exponentialChartMap StandardSemisimpleEmbedding.embedding) 0 :=
  ambientlyDifferentiable.toExponentialChartDifferentiableEmbedding
    |>.hasFDerivAt_zero.differentiableAt

end
end StandardSmoothEmbeddingWitness
end GUT
