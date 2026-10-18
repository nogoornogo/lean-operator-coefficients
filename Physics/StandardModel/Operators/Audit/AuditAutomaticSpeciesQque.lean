import Physics.StandardModel.Operators.AutomaticSpeciesQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Automatic species qque imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.AutomaticSMSpeciesIndex.presentation,
    ``GUT.AutomaticSMSpeciesIndex.continuous,
    ``GUT.AutomaticSMSpeciesIndex.inequivalent,
    ``GUT.AutomaticSMSpeciesIndex.index_character,
    ``GUT.AutomaticSMSpeciesIndex.species_matches,
    ``GUT.AutomaticSpeciesQque.exists_actual_alternation,
    ``GUT.AutomaticSpeciesQque.exists_actual_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Automatic species qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Automatic species qque: {declarations.length} strict axiom checks passed"
