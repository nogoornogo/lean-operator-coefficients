import Physics.StandardModel.Operators.BaryonOne.Qque.SeparatedMediatorQque
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.SeparatedMediatorQque.source_coefficient_eq,
    ``Physics.SeparatedMediatorQque.observer_coefficient_eq,
    ``Physics.SeparatedMediatorQque.sector_eq_of_source,
    ``Physics.SeparatedMediatorQque.sector_eq_of_observer,
    ``Physics.SeparatedMediatorQque.nonzero_of_source]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Separated exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Separated exchange: {declarations.length} strict axiom checks passed"
