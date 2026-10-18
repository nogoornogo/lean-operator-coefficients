import Math.LieGroups.E6.Minuscule.CompactAtlas
import Math.LieGroups.E6.Audit.AuditCompactChart

/-! # E6-0k: translated smooth atlas on the existing compact candidate -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

example : ChartedSpace compactMatrixLieAlgebra compactIdentityComponent := inferInstance

example : IsManifold 𝓘(ℝ, compactMatrixLieAlgebra) ∞ compactIdentityComponent := inferInstance

example (g : compactIdentityComponent) : g ∈ (compactChartAt g).source :=
  mem_compactChartAt_source g

example (g : compactIdentityComponent) : compactChartAt g g = 0 := compactChartAt_self g

example (g h : compactIdentityComponent) (X : compactMatrixLieAlgebra)
    (hX : X ∈ ((compactChartAt g).symm.trans (compactChartAt h)).source) :
    ContDiffAt ℝ ∞ ((compactChartAt g).symm.trans (compactChartAt h)) X :=
  (analyticAt_compact_transition g h X hX).contDiffAt

example : Module.finrank ℝ compactMatrixLieAlgebra = 78 := compactMatrixLieAlgebra_finrank

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactChartLog_eq_extension,
    ``Math.E6.Minuscule.analyticAt_compactLogExtension,
    ``Math.E6.Minuscule.compactChartAt,
    ``Math.E6.Minuscule.compactChartAt_apply,
    ``Math.E6.Minuscule.compactChartAt_symm_apply,
    ``Math.E6.Minuscule.compactChartAt_source,
    ``Math.E6.Minuscule.compactChartAt_target,
    ``Math.E6.Minuscule.mem_compactChartAt_source,
    ``Math.E6.Minuscule.compactChartAt_self,
    ``Math.E6.Minuscule.compactChartedSpace,
    ``Math.E6.Minuscule.compact_transition,
    ``Math.E6.Minuscule.analyticAt_compact_transition,
    ``Math.E6.Minuscule.compactIsManifold,
    ``Math.E6.Minuscule.compactExp_hasStrictFDerivAt_zero]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0k: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0k: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0k: checked {declarations.length} declarations against the standard axiom allowlist"
