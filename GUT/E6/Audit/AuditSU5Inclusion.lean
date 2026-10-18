import GUT.E6.Minuscule.SU5Inclusion
import GUT.Common.StandardChain.StandardChain
import Lean.Util.CollectAxioms

open Math

/-!
# Audit of the actual SU(5) inclusion in the compact E6 candidate

The homomorphism, its continuity and faithfulness are constructed. The
consumer still requires mass and light-target hypotheses; this audit does
not produce a positive-target model or identify the candidate's global form.
-/

set_option autoImplicit false

namespace GUT.E6.Audit

open Math.E6
noncomputable section

open Minuscule Minuscule.SU5Coordinates
open scoped Matrix

example : SU5 →ₜ* compactIdentityComponent := continuousInclusion

example (g : SU5) (v : Fin 27 → ℂ) :
    actualModelEquiv (compactMatrix (inclusion g) *ᵥ v) =
      modelRepresentation g (actualModelEquiv v) := inclusion_intertwining g v

example (X : SpecialUnitaryLieAlgebra.CompactRealForm (Fin 5)) (t : ℝ) :
    groupAction (SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary (t • X)) =
      NormedSpace.exp (t • ambientInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ)) :=
  groupAction_exp X t

-- The finite basis decomposition must not extend from sl(5) to all of gl(5).
example : Matrix.trace (1 : Matrix (Fin 5) (Fin 5) ℂ) ≠ 0 := by
  norm_num [Matrix.trace, Fin.sum_univ_succ]

section Consumer

variable {H E : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ (compactIdentityComponent × H) E)
  (M : StandardChain.Model inclusion rho)

-- No supplied inclusion certificate is required by the continuous wrapper.
example (hc : Continuous (fun p : (compactIdentityComponent × H) × E => rho p.1 p.2)) :
    StandardChain.ContinuousModel inclusion rho where
  toModel := M
  inclusion_injective := inclusion_injective
  inclusion_continuous := inclusion_continuous
  action_continuous := hc

example :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      M.lightSpectrum := M.selection_rule_obstruction

end Consumer

end

end GUT.E6.Audit

run_cmd do
  let declarations := [
    ``GUT.E6.Minuscule.SU5Coordinates.matrixCoordinates_mulVec,
    ``GUT.E6.Minuscule.SU5Coordinates.matrixCoordinates_apply,
    ``GUT.E6.Minuscule.SU5Coordinates.matrixCoordinates_adjoint,
    ``GUT.E6.Minuscule.SU5Coordinates.modelRepresentation_coordinates,
    ``GUT.E6.Minuscule.SU5Coordinates.coordinateAction_eq,
    ``GUT.E6.Minuscule.SU5Coordinates.groupAction_continuous,
    ``GUT.E6.Minuscule.SU5Coordinates.groupAction_injective,
    ``GUT.E6.Minuscule.SU5Coordinates.sourceLine_hasDerivAt,
    ``GUT.E6.Minuscule.SU5Coordinates.representedLine_hasDerivAt,
    ``GUT.E6.Minuscule.SU5Coordinates.representedLine_eq_exp,
    ``GUT.E6.Minuscule.SU5Coordinates.coordinateAction_exp,
    ``GUT.E6.Minuscule.SU5Coordinates.groupAction_exp,
    ``GUT.E6.Minuscule.SU5Coordinates.elementary_comparison,
    ``GUT.E6.Minuscule.SU5Coordinates.elementary_image,
    ``GUT.E6.Minuscule.SU5Coordinates.elementary_image_mem,
    ``GUT.E6.Minuscule.SU5Coordinates.traceless_decomposition,
    ``GUT.E6.Minuscule.SU5Coordinates.ambientInfinitesimal_mem,
    ``GUT.E6.Minuscule.SU5Coordinates.blockMatrix_adjoint,
    ``GUT.E6.Minuscule.SU5Coordinates.ambientInfinitesimal_skew,
    ``GUT.E6.Minuscule.SU5Coordinates.ambientInfinitesimal_compact,
    ``GUT.E6.Minuscule.SU5Coordinates.groupAction_exp_mem,
    ``GUT.E6.Minuscule.SU5Coordinates.groupAction_mem,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_matrix,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_injective,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_continuous,
    ``GUT.E6.Minuscule.SU5Coordinates.continuousInclusion,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_closedEmbedding,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_coordinate_action,
    ``GUT.E6.Minuscule.SU5Coordinates.inclusion_intertwining,
    ``GUT.StandardChain.ContinuousModel.selection_rule_obstruction]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-SU5 inclusion: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-SU5 inclusion: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-SU5 inclusion: checked {declarations.length} declarations"
