import Physics.StandardModel.Spectrum.Representations.NonabelianSMTarget
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-Abelian SM target imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.NonabelianSMTarget.weightCharacter_comp,
    ``Physics.NonabelianSMTarget.index_permute,
    ``Physics.NonabelianSMTarget.target_character_eq,
    ``Physics.NonabelianSMTarget.characters_compatible]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-Abelian SM target: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-Abelian SM target: layer and {declarations.length} strict axiom checks passed"
