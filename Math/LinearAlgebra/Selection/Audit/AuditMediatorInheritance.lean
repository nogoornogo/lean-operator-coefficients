import Math.LinearAlgebra.Selection.MediatorInheritance
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MediatorInheritance.inverse_intertwines,
    ``Math.MediatorInheritance.pairing_of_source_support,
    ``Math.MediatorInheritance.pairing_of_observer_support,
    ``Math.MediatorInheritance.coefficient_of_source_support,
    ``Math.MediatorInheritance.coefficient_of_observer_support,
    ``Math.MediatorInheritance.sumDual_apply,
    ``Math.MediatorInheritance.product_retains_core,
    ``Math.MediatorInheritance.coefficient_product,
    ``Math.MediatorInheritance.spectator_observer_zero,
    ``Math.MediatorInheritance.spectator_source_zero,
    ``Math.MediatorInheritance.duplicate_cancellation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator inheritance: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator inheritance: {declarations.length} strict axiom checks passed"
