import Physics.StandardModel.Operators.MediatorFullLightCertificate
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.MediatorFullLightCertificate.ofRestriction,
    ``GUT.MediatorFullLightCertificate.Certificate.generated_nonzero,
    ``GUT.MediatorFullLightCertificate.Certificate.reconstruct,
    ``GUT.MediatorFullLightCertificate.Certificate.residualHom_nonzero,
    ``GUT.MediatorFullLightCertificate.Certificate.hasCoefficient,
    ``GUT.MediatorFullLightCertificate.Certificate.hasResidualMap]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator full light certificate: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator full light certificate: {declarations.length} strict axiom checks passed"
