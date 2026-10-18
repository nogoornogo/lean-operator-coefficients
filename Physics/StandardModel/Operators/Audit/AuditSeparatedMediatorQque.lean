import Physics.StandardModel.Operators.SeparatedMediatorQque
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SeparatedMediatorQque.source_coefficient_eq,
    ``GUT.SeparatedMediatorQque.observer_coefficient_eq,
    ``GUT.SeparatedMediatorQque.sector_eq_of_source,
    ``GUT.SeparatedMediatorQque.sector_eq_of_observer,
    ``GUT.SeparatedMediatorQque.nonzero_of_source]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Separated exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Separated exchange: {declarations.length} strict axiom checks passed"
