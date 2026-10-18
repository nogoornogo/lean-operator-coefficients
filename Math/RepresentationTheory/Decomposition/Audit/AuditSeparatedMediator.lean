import Math.RepresentationTheory.Decomposition.SeparatedMediator
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.SeparatedMediator.map_zero,
    ``Math.SeparatedMediator.core_stable,
    ``Math.SeparatedMediator.projection_stable,
    ``Math.SeparatedMediator.source_support,
    ``Math.SeparatedMediator.dual_support,
    ``Math.SeparatedMediator.coreMass,
    ``Math.SeparatedMediator.coreMass_apply,
    ``Math.SeparatedMediator.coreMass_compat,
    ``Math.SeparatedMediator.repeatedSwap_core_zero,
    ``Math.SeparatedMediator.repeatedSwap_moves]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Separated exchange: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Separated exchange: {declarations.length} strict axiom checks passed"
