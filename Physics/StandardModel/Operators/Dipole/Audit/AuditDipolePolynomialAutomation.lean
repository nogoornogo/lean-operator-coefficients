import Physics.StandardModel.Operators.Dipole.DipolePolynomialAutomationExamples
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole polynomial automation imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.PolynomialBasisCoordinates.coordinate,
    ``Math.PolynomialBasisCoordinates.expansion,
    ``Physics.DipolePolynomialAutomation.register,
    ``Physics.DipolePolynomialAutomation.residual_expansion,
    ``Physics.DipolePolynomialAutomation.certificate,
    ``Physics.DipolePolynomialAutomation.selected,
    ``Physics.DipolePolynomialAutomation.exists_nonzero_iff,
    ``Physics.DipoleModelInterface.PolynomialCertificate.withCoefficients,
    ``Physics.DipolePolynomialAutomationExamples.cubicCertificate,
    ``Physics.DipolePolynomialAutomationExamples.cubic_selected,
    ``Physics.DipolePolynomialAutomationExamples.cubic_realized,
    ``Physics.DipolePolynomialAutomationExamples.correspondence,
    ``Physics.DipolePolynomialAutomationExamples.externalCertificate,
    ``Physics.DipolePolynomialAutomationExamples.external_realized,
    ``Physics.DipolePolynomialAutomationExamples.cancellingCertificate,
    ``Physics.DipolePolynomialAutomationExamples.cancelling_selected,
    ``Physics.DipolePolynomialAutomationExamples.cancelling_grouped_zero,
    ``Physics.DipolePolynomialAutomationExamples.finite_domain_no_nonzero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole polynomial automation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole polynomial automation: {declarations.length} strict transitive axiom checks passed"
