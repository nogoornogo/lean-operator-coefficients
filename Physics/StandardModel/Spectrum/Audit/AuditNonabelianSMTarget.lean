import Physics.StandardModel.Spectrum.NonabelianSMTarget
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-Abelian SM target imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.NonabelianSMTarget.weightCharacter_comp,
    ``GUT.NonabelianSMTarget.index_permute,
    ``GUT.NonabelianSMTarget.target_character_eq,
    ``GUT.NonabelianSMTarget.characters_compatible]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-Abelian SM target: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-Abelian SM target: layer and {declarations.length} strict axiom checks passed"
