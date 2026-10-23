import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQque
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.MediatorQque.equivariantInternal_linear,
    ``Physics.MediatorQque.invariant_of_equivariant,
    ``Physics.MediatorQque.sector,
    ``Physics.MediatorQque.ordered_eq_action,
    ``Physics.MediatorQque.hom,
    ``Physics.MediatorQque.reconstruct,
    ``Physics.MediatorQque.hom_eq_zero_iff,
    ``Physics.MediatorQque.hom_ne_zero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator exchange: {declarations.length} strict axiom checks passed"
