import Math.LieGroups.E6.Minuscule.CompactNormalizer
import Math.LieGroups.Matrix.MatrixLieGroupComponent

/-!
# Connected compact candidate and its exact exponential directions

Taking the identity component supplies connectedness, not simple
connectedness, an order-three center, or a named compact E6 identification.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

abbrev compactIdentityComponent : Subgroup compactNormalizer :=
  MatrixLieGroupNormalizer.identityComponent compactMatrixLieAlgebra

abbrev compactIdentityMatrices : Submonoid Matrix27 :=
  MatrixLieGroupNormalizer.componentMatrices compactMatrixLieAlgebra

theorem compactIdentityComponent_isClosed :
    IsClosed (compactIdentityComponent : Set compactNormalizer) :=
  MatrixLieGroupNormalizer.isClosed_identityComponent compactMatrixLieAlgebra

theorem compactIdentityComponent_isCompact :
    IsCompact (compactIdentityComponent : Set compactNormalizer) :=
  compactIdentityComponent_isClosed.isCompact

theorem mem_compactMatrix_iff_exp_mem_identityComponent (X : Matrix27) :
    X ∈ compactMatrixLieAlgebra ↔ ∀ t : ℝ, exp (t • X) ∈ compactIdentityMatrices :=
  (mem_compactMatrix_iff_exp_mem_normalizer X).trans
    (MatrixLieGroupNormalizer.exp_mem_componentMatrices_iff compactMatrixLieAlgebra X).symm

theorem exp_compactRealForm_mem_identityComponent (X : compactRealForm) (t : ℝ) :
    exp (t • X.val.val) ∈ compactIdentityMatrices :=
  (mem_compactMatrix_iff_exp_mem_identityComponent _).mp ⟨X, rfl⟩ t

theorem exp_generator_mem_identityComponent (k : Fin 3) (i : Fin 6) (t : ℝ) :
    exp (t • (compactGeneratorElement k i).val.val) ∈ compactIdentityMatrices :=
  exp_compactRealForm_mem_identityComponent _ t

end

end Math.E6.Minuscule
