import GUT.E6.Minuscule.SU5LieImage
import Math.LieGroups.E6.Minuscule.CompactLieGroup
import GUT.SU6.Embeddings.SpecialUnitaryGeneration

open Math

/-!
# An actual SU(5) inclusion into the compact E6 candidate

Membership follows from represented exponentials and the proved real Lie
image. This does not identify the candidate's global form with simply connected E6.
-/

set_option autoImplicit false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open SpecialUnitaryLieAlgebra NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

theorem groupAction_exp_mem (X : CompactRealForm (Fin 5)) :
    groupAction (CompactRealForm.expSpecialUnitary X) ∈ compactIdentityMatrices := by
  have h := (mem_compactMatrix_iff_exp_mem_identityComponent _).mp
    (ambientInfinitesimal_compact X) 1
  have he := groupAction_exp X 1
  simp only [one_smul] at he h
  rw [he]
  exact h

theorem groupAction_mem (g : SU5) : groupAction g ∈ compactIdentityMatrices := by
  rw [← SpecialUnitaryGeneration.expSpecialUnitary_centered_mul_correction g, map_mul]
  exact compactIdentityMatrices.mul_mem (groupAction_exp_mem _) (groupAction_exp_mem _)

private def inclusionElement (g : SU5) : compactIdentityComponent :=
  let h := (MatrixLieGroupNormalizer.mem_componentMatrices compactMatrixLieAlgebra _).mp
    (groupAction_mem g)
  ⟨h.choose, h.choose_spec.1⟩

private theorem inclusionElement_matrix (g : SU5) :
    compactMatrix (inclusionElement g) = groupAction g :=
  ((MatrixLieGroupNormalizer.mem_componentMatrices compactMatrixLieAlgebra _).mp
    (groupAction_mem g)).choose_spec.2

/-- This is a constructed group homomorphism, not an inclusion certificate. -/
def inclusion : SU5 →* compactIdentityComponent where
  toFun := inclusionElement
  map_one' := by
    apply compactMatrix_injective
    rw [inclusionElement_matrix, compactMatrix_one, map_one]
  map_mul' g h := by
    apply compactMatrix_injective
    rw [compactMatrix_mul, inclusionElement_matrix, inclusionElement_matrix,
      inclusionElement_matrix, map_mul]

@[simp] theorem inclusion_matrix (g : SU5) : compactMatrix (inclusion g) = groupAction g :=
  inclusionElement_matrix g

theorem inclusion_injective : Function.Injective inclusion := by
  intro g h he
  apply groupAction_injective
  simpa only [inclusion_matrix] using congrArg compactMatrix he

theorem inclusion_continuous : Continuous inclusion := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun g => compactMatrix (inclusion g))
  simpa only [inclusion_matrix] using groupAction_continuous

def continuousInclusion : SU5 →ₜ* compactIdentityComponent :=
  ⟨inclusion, inclusion_continuous⟩

theorem inclusion_closedEmbedding : Topology.IsClosedEmbedding inclusion :=
  inclusion_continuous.isClosedEmbedding inclusion_injective

theorem inclusion_coordinate_action (g : SU5) :
    matrixCoordinates (compactMatrix (inclusion g)) = actionBlock g := by
  rw [inclusion_matrix]
  change matrixCoordinates (matrixCoordinates.symm (coordinateAction g)) = _
  rw [matrixCoordinates.apply_symm_apply, coordinateAction_eq]

/-- The actual restricted group action, not just the infinitesimal generators. -/
theorem inclusion_intertwining (g : SU5) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactMatrix (inclusion g) *ᵥ v) =
      modelRepresentation g (actualModelEquiv v) := by
  apply modelCoordinates.injective
  rw [modelRepresentation_coordinates]
  have h := matrixCoordinates_mulVec (compactMatrix (inclusion g)) v
  rw [inclusion_coordinate_action] at h
  simpa [actualModelEquiv] using h.symm

end

end GUT.E6.Minuscule.SU5Coordinates
