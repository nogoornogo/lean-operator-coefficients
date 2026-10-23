import Math.LinearAlgebra.Selection.MediatorTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MediatorTransport.mass_apply,
    ``Math.MediatorTransport.inverse_apply,
    ``Math.MediatorTransport.observer_apply,
    ``Math.MediatorTransport.action_eq,
    ``Math.MediatorTransport.coefficient_eq,
    ``Math.MediatorTransport.mass_refl,
    ``Math.MediatorTransport.source_refl,
    ``Math.MediatorTransport.observer_refl,
    ``Math.MediatorTransport.mass_trans,
    ``Math.MediatorTransport.source_trans,
    ``Math.MediatorTransport.observer_trans,
    ``Math.MediatorTransport.untransported_dual_control,
    ``Math.MediatorTransport.nondiagonal_mass_control]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator transport: {declarations.length} strict axiom checks passed"
