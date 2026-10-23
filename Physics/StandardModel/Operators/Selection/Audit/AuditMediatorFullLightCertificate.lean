import Physics.StandardModel.Operators.Selection.MediatorFullLightCertificate
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.MediatorFullLightCertificate.ofRestriction,
    ``Physics.MediatorFullLightCertificate.Certificate.generated_nonzero,
    ``Physics.MediatorFullLightCertificate.Certificate.reconstruct,
    ``Physics.MediatorFullLightCertificate.Certificate.residualHom_nonzero,
    ``Physics.MediatorFullLightCertificate.Certificate.hasCoefficient,
    ``Physics.MediatorFullLightCertificate.Certificate.hasResidualMap]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator full light certificate: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator full light certificate: {declarations.length} strict axiom checks passed"
