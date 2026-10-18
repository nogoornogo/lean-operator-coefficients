import GUT.SU5.Matching.SeparatedExchange
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.SeparatedExchange.nonzero_of_source_separation,
    ``GUT.SU5.SeparatedExchange.nonzero_of_observer_separation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Separated exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Separated exchange: {declarations.length} strict axiom checks passed"
