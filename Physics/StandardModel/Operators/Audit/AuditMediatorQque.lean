import Physics.StandardModel.Operators.MediatorQque
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.MediatorQque.equivariantInternal_linear,
    ``GUT.MediatorQque.invariant_of_equivariant,
    ``GUT.MediatorQque.sector,
    ``GUT.MediatorQque.ordered_eq_action,
    ``GUT.MediatorQque.hom,
    ``GUT.MediatorQque.reconstruct,
    ``GUT.MediatorQque.hom_eq_zero_iff,
    ``GUT.MediatorQque.hom_ne_zero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator exchange: {declarations.length} strict axiom checks passed"
