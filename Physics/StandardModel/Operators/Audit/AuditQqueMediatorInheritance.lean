import Physics.StandardModel.Operators.QqueMediatorInheritance
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.QqueMediatorInheritance.invariant,
    ``GUT.QqueMediatorInheritance.internal_eq,
    ``GUT.QqueMediatorInheritance.sector_eq]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator inheritance: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator inheritance: {declarations.length} strict axiom checks passed"
