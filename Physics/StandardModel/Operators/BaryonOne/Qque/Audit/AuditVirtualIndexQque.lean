import Physics.StandardModel.Operators.BaryonOne.Qque.VirtualIndexQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

#check Physics.VirtualIndexQque.exists_actual_alternation_of_common_index
#check Physics.VirtualIndexQque.exists_actual_exterior

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Virtual qque imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.VirtualSMSpeciesIndex.WeightMatches,
    ``Physics.VirtualSMSpeciesIndex.SpeciesMatches,
    ``Physics.VirtualSMSpeciesIndex.characters_compatible,
    ``Physics.VirtualSMSpeciesIndex.common_quotient,
    ``Physics.VirtualIndexQque.exists_actual_alternation_of_common_index,
    ``Physics.VirtualIndexQque.exists_actual_alternation,
    ``Physics.VirtualIndexQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Virtual qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Virtual qque: {declarations.length} strict axiom checks passed"
