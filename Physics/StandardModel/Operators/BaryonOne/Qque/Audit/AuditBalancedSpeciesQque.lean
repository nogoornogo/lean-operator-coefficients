import Physics.StandardModel.Operators.BaryonOne.Qque.BalancedSpeciesQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Balanced species imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.BalancedSpeciesExtension.refl,
    ``Physics.BalancedSpeciesExtension.not_exact_of_quark_extra,
    ``Physics.BalancedSpeciesExtension.shared_positive,
    ``Physics.BalancedSpeciesExtension.pairwise_positive,
    ``Physics.BalancedSpeciesQque.exists_actual_alternation,
    ``Physics.BalancedSpeciesQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Balanced species: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Balanced species: {declarations.length} strict axiom checks passed"
