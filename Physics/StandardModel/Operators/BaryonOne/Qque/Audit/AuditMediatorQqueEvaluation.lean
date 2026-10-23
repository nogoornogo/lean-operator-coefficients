import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQqueEvaluation
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.MediatorQqueEvaluation.sector_slots,
    ``Physics.MediatorQqueEvaluation.sector_ne_zero_of_slots,
    ``Physics.MediatorQqueEvaluation.sector_ne_zero_of_restriction]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator evaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator evaluation: {declarations.length} strict axiom checks passed"
