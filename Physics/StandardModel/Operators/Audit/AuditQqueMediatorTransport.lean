import Physics.StandardModel.Operators.QqueMediatorTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.QqueMediatorTransport.invariant,
    ``GUT.QqueMediatorTransport.generated_eq,
    ``GUT.QqueMediatorTransport.generated_ne_zero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Qque transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qque transport: {declarations.length} strict axiom checks passed"
