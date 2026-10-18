import Physics.StandardModel.Operators.BalancedSpeciesQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Balanced species imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.BalancedSpeciesExtension.refl,
    ``GUT.BalancedSpeciesExtension.not_exact_of_quark_extra,
    ``GUT.BalancedSpeciesExtension.shared_positive,
    ``GUT.BalancedSpeciesExtension.pairwise_positive,
    ``GUT.BalancedSpeciesQque.exists_actual_alternation,
    ``GUT.BalancedSpeciesQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Balanced species: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Balanced species: {declarations.length} strict axiom checks passed"
