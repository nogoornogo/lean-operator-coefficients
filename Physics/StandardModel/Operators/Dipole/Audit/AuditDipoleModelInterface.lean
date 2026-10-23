import Physics.StandardModel.Operators.Dipole.DipoleModelExamples
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole model interface imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.DipoleModelInterface.Registered.selected,
    ``Physics.DipoleModelInterface.Registered.nonzero_iff,
    ``Physics.DipoleModelInterface.Registered.nonzero_of_channel,
    ``Physics.DipoleModelInterface.Registered.forbidden_of_distinct_weights,
    ``Physics.DipoleModelInterface.Registered.restrict,
    ``Physics.DipoleModelInterface.Registered.nonzero_restrict_iff,
    ``Physics.DipoleModelInterface.Registered.pullback,
    ``Physics.DipoleModelInterface.Registered.observe_pullback,
    ``Physics.DipoleModelInterface.Registered.nonzero_pullback_iff,
    ``Physics.DipoleModelInterface.Registered.exists_pullback_iff,
    ``Physics.DipoleModelInterface.Registered.withCoefficients,
    ``Physics.DipoleModelInterface.Registered.nonzero_withCoefficients_iff,
    ``Physics.DipoleModelInterface.ofResidual,
    ``Physics.DipoleModelInterface.ofCouplings,
    ``Physics.DipoleModelInterface.PolynomialCertificate.exists_nonzero_iff,
    ``Physics.DipoleModelInterface.PolynomialCertificate.no_nonzero_iff,
    ``Math.MatrixIntertwiner.ofMatrix,
    ``Math.MatrixIntertwiner.entry,
    ``Physics.DipoleMatrixInterface.register,
    ``Physics.DipoleMatrixInterface.selected_entry,
    ``Physics.DipoleModelExamples.external_nonzero_iff,
    ``Physics.DipoleModelExamples.correlated_selected,
    ``Physics.DipoleModelExamples.correlated_nonzero_iff,
    ``Physics.DipoleModelExamples.cubicCertificate,
    ``Physics.DipoleModelExamples.cubic_realized,
    ``Physics.DipoleModelExamples.cancellingCertificate,
    ``Physics.DipoleModelExamples.cancelling_no_nonzero,
    ``Physics.DipoleModelExamples.matrix_selected,
    ``Physics.DipoleModelExamples.matrix_nonzero_iff,
    ``Physics.DipoleModelExamples.restricted_zero_unreachable]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole model interface: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole model interface: {declarations.length} strict transitive axiom checks passed"
