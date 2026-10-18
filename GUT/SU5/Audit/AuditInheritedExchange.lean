import GUT.SU5.Matching.InheritedExchange
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.InheritedExchange.nonzero_of_projection,
    ``GUT.SU5.InheritedExchange.spectator_invariant,
    ``GUT.SU5.InheritedExchange.spectatorSector_eq,
    ``GUT.SU5.InheritedExchange.spectatorSector_nonzero,
    ``GUT.SU5.InheritedExchange.retained_core_can_cancel]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator inheritance: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator inheritance: {declarations.length} strict axiom checks passed"
