import Math.LieGroups.E6.Minuscule.CompactChart
import Math.LieGroups.E6.Audit.AuditCompactLocalLog

/-! # E6-0j: actual open exponential coordinates, not a supplied chart certificate -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

example : Module.finrank ℝ compactMatrixLieAlgebra = 78 := compactMatrixLieAlgebra_finrank

example : compactExpChart 0 = 1 := by simp

example : compactExpChart.symm 1 = 0 := by simp

example : IsOpen compactExpChart.source := compactExpChart.open_source

example : IsOpen compactExpChart.target := compactExpChart.open_target

example (X : compactMatrixLieAlgebra) (hX : X ∈ compactExpChart.source) :
    compactChartLog (compactExp X) = X := by
  simpa using compactExpChart.left_inv hX

example (g : compactIdentityComponent) (hg : g ∈ compactExpChart.target) :
    compactExp (compactChartLog g) = g := by
  simpa using compactExpChart.right_inv hg

example (g : compactIdentityComponent) (hg : g ∈ compactExpChart.target) :
    (compactExpChart.symm g : Matrix27) =
      NormedSpace.log (g.val.val : Matrix27) :=
  compactExpChart_symm_coe g hg

example : ¬∀ X : Matrix27, exp X ∈ compactNormalizerMatrices → X ∈ compactMatrixLieAlgebra :=
  no_global_exp_converse

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.LocalInverseChart.ofOpen,
    ``Math.LocalInverseChart.exists_chart_within,
    ``Math.E6.Minuscule.compactExp_coe,
    ``Math.E6.Minuscule.compactExp_zero,
    ``Math.E6.Minuscule.compactExp_continuous,
    ``Math.E6.Minuscule.compactChartLog_one,
    ``Math.E6.Minuscule.eventually_compactChartLog_coe,
    ``Math.E6.Minuscule.eventually_compactChartLog_continuousAt,
    ``Math.E6.Minuscule.eventually_compactChartLog_compactExp,
    ``Math.E6.Minuscule.eventually_compactExp_compactChartLog,
    ``Math.E6.Minuscule.eventually_analyticAt_compactMatrixLog,
    ``Math.E6.Minuscule.exists_compactExpChart,
    ``Math.E6.Minuscule.compactExpChart,
    ``Math.E6.Minuscule.compactExpChart_apply,
    ``Math.E6.Minuscule.compactExpChart_symm_apply,
    ``Math.E6.Minuscule.zero_mem_compactExpChart_source,
    ``Math.E6.Minuscule.one_mem_compactExpChart_target,
    ``Math.E6.Minuscule.compactExpChart_symm_coe,
    ``Math.E6.Minuscule.analyticAt_logOn_compactExpChart_target]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0j: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0j: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0j: checked {declarations.length} declarations against the standard axiom allowlist"
