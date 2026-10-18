import Physics.StandardModel.Operators.VirtualIndexQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

#check GUT.VirtualIndexQque.exists_actual_alternation_of_common_index
#check GUT.VirtualIndexQque.exists_actual_exterior

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Virtual qque imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.VirtualSMSpeciesIndex.WeightMatches,
    ``GUT.VirtualSMSpeciesIndex.SpeciesMatches,
    ``GUT.VirtualSMSpeciesIndex.characters_compatible,
    ``GUT.VirtualSMSpeciesIndex.common_quotient,
    ``GUT.VirtualIndexQque.exists_actual_alternation_of_common_index,
    ``GUT.VirtualIndexQque.exists_actual_alternation,
    ``GUT.VirtualIndexQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Virtual qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Virtual qque: {declarations.length} strict axiom checks passed"
