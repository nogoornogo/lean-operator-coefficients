import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM
import Physics.FieldTheory.Jets.Gauge.FormalYangMills
import Physics.FieldTheory.Jets.Gauge.YangMillsControls

/-! Explicit public declaration inventory, strict transitive axiom and layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.PolynomialScalarEOM.OffShell,
    ``Physics.PolynomialScalarEOM.D,
    ``Physics.PolynomialScalarEOM.field,
    ``Physics.PolynomialScalarEOM.seed,
    ``Physics.PolynomialScalarEOM.equations,
    ``Physics.PolynomialScalarEOM.ideal,
    ``Physics.PolynomialScalarEOM.Shell,
    ``Physics.PolynomialScalarEOM.projection,
    ``Physics.PolynomialScalarEOM.integrated,
    ``Physics.PolynomialScalarEOM.seed_zero,
    ``Physics.PolynomialScalarEOM.descendants_zero,
    ``Physics.PolynomialScalarEOM.zeroEvaluation_seed,
    ``Physics.PolynomialScalarEOM.unit_survives,
    ``Physics.PolynomialScalarEOM.offAction,
    ``Physics.PolynomialScalarEOM.field_invariant,
    ``Physics.PolynomialScalarEOM.seed_invariant,
    ``Physics.PolynomialScalarEOM.ideal_invariant,
    ``Physics.PolynomialScalarEOM.lorentzTransport,
    ``Physics.PolynomialScalarEOM.derivative_covariance,
    ``Physics.PolynomialScalarEOM.lorentzIBPTransport,
    ``Physics.PolynomialScalarEOM.finiteImage,
    ``Physics.PolynomialScalarEOM.finiteImage_finite,
    ``Physics.PolynomialScalarEOM.sourceEquiv,
    ``Physics.PolynomialScalarEOM.coefficientEquiv,
    ``Physics.PolynomialScalarEOM.kinetic_relation,
    ``Physics.PolynomialScalarEOM.kinetic_mod_ibp,
    ``Physics.FormalYangMills.Components,
    ``Physics.FormalYangMills.OffShell,
    ``Physics.FormalYangMills.Mat,
    ``Physics.FormalYangMills.D,
    ``Physics.FormalYangMills.ordinary,
    ``Physics.FormalYangMills.connection,
    ``Physics.FormalYangMills.F,
    ``Physics.FormalYangMills.nabla,
    ``Physics.FormalYangMills.sign,
    ``Physics.FormalYangMills.equation,
    ``Physics.FormalYangMills.equations,
    ``Physics.FormalYangMills.ideal,
    ``Physics.FormalYangMills.Shell,
    ``Physics.FormalYangMills.projection,
    ``Physics.FormalYangMills.curvature_antisymmetric,
    ``Physics.FormalYangMills.commutator,
    ``Physics.FormalYangMills.bianchi,
    ``Physics.FormalYangMills.equation_mem,
    ``Physics.FormalYangMills.descendants_zero,
    ``Physics.FormalYangMills.entriesMem,
    ``Physics.FormalYangMills.entries_mul_left,
    ``Physics.FormalYangMills.entries_mul_right,
    ``Physics.FormalYangMills.entries_nabla,
    ``Physics.FormalYangMills.covariantWord,
    ``Physics.FormalYangMills.covariant_descendants_mem,
    ``Physics.FormalYangMills.covariant_descendants_zero,
    ``Physics.FormalYangMills.zeroEvaluation_connection,
    ``Physics.FormalYangMills.zeroEvaluation_F,
    ``Physics.FormalYangMills.zeroEvaluation_equation,
    ``Physics.FormalYangMills.unit_survives,
    ``Physics.FormalYangMills.sourceEquiv,
    ``Physics.FormalYangMills.coefficientEquiv,
    ``Physics.FormalYangMills.projection_kernel,
    ``Physics.FormalYangMills.projection_surjective,
    ``Physics.FormalYangMills.finiteImage,
    ``Physics.FormalYangMills.finiteImage_finite,
    ``Physics.FormalYangMills.Controls.N,
    ``Physics.FormalYangMills.Controls.values,
    ``Physics.FormalYangMills.Controls.evaluation,
    ``Physics.FormalYangMills.Controls.matrixEvaluation,
    ``Physics.FormalYangMills.Controls.evaluation_derivative,
    ``Physics.FormalYangMills.Controls.evaluation_connection,
    ``Physics.FormalYangMills.Controls.evaluation_F,
    ``Physics.FormalYangMills.Controls.evaluation_nabla,
    ``Physics.FormalYangMills.Controls.curvature_evaluation,
    ``Physics.FormalYangMills.Controls.equation_evaluation,
    ``Physics.FormalYangMills.Controls.offShell_equation_nonzero,
    ``Physics.FormalYangMills.Controls.onShell_equation_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Polynomial scalar and formal Yang-Mills: {ds.length} strict transitive checks passed"
