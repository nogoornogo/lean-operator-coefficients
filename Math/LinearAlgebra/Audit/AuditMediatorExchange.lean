import Math.LinearAlgebra.MediatorExchange
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MediatorExchange.scalarMass_apply,
    ``Math.MediatorExchange.scalarMass_symm_apply,
    ``Math.MediatorExchange.shifted_action,
    ``Math.MediatorExchange.on_shell,
    ``Math.MediatorExchange.left_equation,
    ``Math.MediatorExchange.right_equation,
    ``Math.MediatorExchange.coefficient_tmul,
    ``Math.MediatorExchange.coefficient_eq_action,
    ``Math.MediatorExchange.coefficient_eq_zero_iff,
    ``Math.MediatorExchange.on_shell_transport,
    ``Math.MediatorExchange.cancellation_control]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator exchange: {declarations.length} strict axiom checks passed"
