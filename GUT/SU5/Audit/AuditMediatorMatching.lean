import GUT.SU5.Matching.MediatorMatching
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.MediatorMatching.current_pair,
    ``GUT.SU5.MediatorMatching.coefficient_eq,
    ``GUT.SU5.MediatorMatching.invariant,
    ``GUT.SU5.MediatorMatching.internal_eq,
    ``GUT.SU5.MediatorMatching.generated_eq,
    ``GUT.SU5.MediatorMatching.generated_nonzero,
    ``GUT.SU5.MediatorMatching.ordered_eq_original_action]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mediator exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mediator exchange: {declarations.length} strict axiom checks passed"
