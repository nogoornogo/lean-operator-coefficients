import Math.LieGroups.E6.Minuscule.CompactLieGroup
import Math.LieGroups.E6.Audit.AuditCompactAtlas

/-! # E6-0l: smooth group operations with no supplied smoothness certificate -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

example : LieGroup 𝓘(ℝ, compactMatrixLieAlgebra) ∞ compactIdentityComponent := inferInstance

example : CompactSpace compactIdentityComponent := inferInstance

example : ConnectedSpace compactIdentityComponent := inferInstance

example : Function.Injective compactMatrix := compactMatrix_injective

example : ContMDiff 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) ∞ compactMatrix :=
  contMDiff_compactMatrix

example : ContMDiff (𝓘(ℝ, compactMatrixLieAlgebra).prod 𝓘(ℝ, compactMatrixLieAlgebra))
    𝓘(ℝ, compactMatrixLieAlgebra) ∞
    (fun p : compactIdentityComponent × compactIdentityComponent => p.1 * p.2) :=
  contMDiff_compact_mul

example : ContMDiff 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, compactMatrixLieAlgebra) ∞
    (fun g : compactIdentityComponent => g⁻¹) := contMDiff_compact_inv

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactMatrix_one,
    ``Math.E6.Minuscule.compactMatrix_mul,
    ``Math.E6.Minuscule.compactMatrix_inv,
    ``Math.E6.Minuscule.compactMatrix_continuous,
    ``Math.E6.Minuscule.compactMatrix_injective,
    ``Math.E6.Minuscule.compact_extChartAt_apply,
    ``Math.E6.Minuscule.compact_extChartAt_symm_apply,
    ``Math.E6.Minuscule.contMDiff_compactMatrix,
    ``Math.E6.Minuscule.contMDiffAt_of_compactMatrix,
    ``Math.E6.Minuscule.contMDiff_compact_mul,
    ``Math.E6.Minuscule.contMDiff_compact_inv,
    ``Math.E6.Minuscule.compactLieGroup]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0l: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0l: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0l: checked {declarations.length} declarations against the standard axiom allowlist"
