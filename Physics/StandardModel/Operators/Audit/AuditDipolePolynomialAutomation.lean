import Physics.StandardModel.Operators.DipolePolynomialAutomationExamples
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
    ``GUT.DipolePolynomialAutomation.register,
    ``GUT.DipolePolynomialAutomation.residual_expansion,
    ``GUT.DipolePolynomialAutomation.certificate,
    ``GUT.DipolePolynomialAutomation.selected,
    ``GUT.DipolePolynomialAutomation.exists_nonzero_iff,
    ``GUT.DipoleModelInterface.PolynomialCertificate.withCoefficients,
    ``GUT.DipolePolynomialAutomationExamples.cubicCertificate,
    ``GUT.DipolePolynomialAutomationExamples.cubic_selected,
    ``GUT.DipolePolynomialAutomationExamples.cubic_realized,
    ``GUT.DipolePolynomialAutomationExamples.correspondence,
    ``GUT.DipolePolynomialAutomationExamples.externalCertificate,
    ``GUT.DipolePolynomialAutomationExamples.external_realized,
    ``GUT.DipolePolynomialAutomationExamples.cancellingCertificate,
    ``GUT.DipolePolynomialAutomationExamples.cancelling_selected,
    ``GUT.DipolePolynomialAutomationExamples.cancelling_grouped_zero,
    ``GUT.DipolePolynomialAutomationExamples.finite_domain_no_nonzero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole polynomial automation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole polynomial automation: {declarations.length} strict transitive axiom checks passed"
