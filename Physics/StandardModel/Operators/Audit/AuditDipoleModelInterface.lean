import Physics.StandardModel.Operators.DipoleModelExamples
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole model interface imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.DipoleModelInterface.Registered.selected,
    ``GUT.DipoleModelInterface.Registered.nonzero_iff,
    ``GUT.DipoleModelInterface.Registered.nonzero_of_channel,
    ``GUT.DipoleModelInterface.Registered.forbidden_of_distinct_weights,
    ``GUT.DipoleModelInterface.Registered.restrict,
    ``GUT.DipoleModelInterface.Registered.nonzero_restrict_iff,
    ``GUT.DipoleModelInterface.Registered.pullback,
    ``GUT.DipoleModelInterface.Registered.observe_pullback,
    ``GUT.DipoleModelInterface.Registered.nonzero_pullback_iff,
    ``GUT.DipoleModelInterface.Registered.exists_pullback_iff,
    ``GUT.DipoleModelInterface.Registered.withCoefficients,
    ``GUT.DipoleModelInterface.Registered.nonzero_withCoefficients_iff,
    ``GUT.DipoleModelInterface.ofResidual,
    ``GUT.DipoleModelInterface.ofCouplings,
    ``GUT.DipoleModelInterface.PolynomialCertificate.exists_nonzero_iff,
    ``GUT.DipoleModelInterface.PolynomialCertificate.no_nonzero_iff,
    ``Math.MatrixIntertwiner.ofMatrix,
    ``Math.MatrixIntertwiner.entry,
    ``GUT.DipoleMatrixInterface.register,
    ``GUT.DipoleMatrixInterface.selected_entry,
    ``GUT.DipoleModelExamples.external_nonzero_iff,
    ``GUT.DipoleModelExamples.correlated_selected,
    ``GUT.DipoleModelExamples.correlated_nonzero_iff,
    ``GUT.DipoleModelExamples.cubicCertificate,
    ``GUT.DipoleModelExamples.cubic_realized,
    ``GUT.DipoleModelExamples.cancellingCertificate,
    ``GUT.DipoleModelExamples.cancelling_no_nonzero,
    ``GUT.DipoleModelExamples.matrix_selected,
    ``GUT.DipoleModelExamples.matrix_nonzero_iff,
    ``GUT.DipoleModelExamples.restricted_zero_unreachable]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole model interface: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole model interface: {declarations.length} strict transitive axiom checks passed"
