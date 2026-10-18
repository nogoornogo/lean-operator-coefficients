import Math.LieGroups.E6.Minuscule.CompactTangent
import Math.LieGroups.E6.Audit.AuditCompactLieGroup
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Adjoint.Units.Basic

/-!
# E6-0m: actual tangent image and pinned bracket-bridge ingredients

The imported Lie functor and units commutator theorem are audited as
ingredients, not misreported as an implemented candidate-group bridge.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

example : mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1 =
    compactTangentInclusion := mfderiv_compactMatrix_one

example : Function.Injective
    (mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1) :=
  mfderiv_compactMatrix_one_injective

example (A : Matrix27) :
    (∃ v, tangentSpaceCastModel 𝓘(ℝ, Matrix27) (compactMatrix 1)
      (mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1 v) = A) ↔
      A ∈ compactMatrixLieAlgebra := exists_tangent_matrix_iff A

example : Module.finrank ℝ
    (TangentSpace 𝓘(ℝ, compactMatrixLieAlgebra) (1 : compactIdentityComponent)) = 78 :=
  compactTangentEquiv.toLinearEquiv.finrank_eq.trans compactMatrixLieAlgebra_finrank

example : ¬∀ X : Matrix27, NormedSpace.exp X ∈ compactNormalizerMatrices →
    X ∈ compactMatrixLieAlgebra := no_global_exp_converse

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactMatrix_writtenInExtChartAt_one,
    ``Math.E6.Minuscule.compactTangentInclusion,
    ``Math.E6.Minuscule.mfderiv_compactMatrix_one,
    ``Math.E6.Minuscule.compactTangentEquiv,
    ``Math.E6.Minuscule.compactTangent_matrix,
    ``Math.E6.Minuscule.mfderiv_compactMatrix_one_injective,
    ``Math.E6.Minuscule.exists_tangent_matrix_iff,
    ``lieMap,
    ``leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
    ``TauCeti.Lie.groupLieAlgebra_units_ad_apply,
    ``TauCeti.Lie.unitsLieAlgebraLieEquiv]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0m: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0m: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0m: checked {declarations.length} declarations against the standard axiom allowlist"
