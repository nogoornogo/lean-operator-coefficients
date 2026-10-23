import Physics.StandardModel.Spectrum.Representations.NonabelianAbelianRecovery
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM Abelian recovery imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.NonabelianAbelianRecovery.keyCharacter_joint,
    ``Physics.NonabelianAbelianRecovery.actualSpectrum_apply,
    ``Physics.NonabelianAbelianRecovery.actualSpectrum_neg_apply,
    ``Physics.NonabelianAbelianRecovery.targetProfiles_apply,
    ``Physics.NonabelianAbelianRecovery.speciesProfile_total,
    ``Physics.NonabelianAbelianRecovery.speciesProfile_positive_iff,
    ``Physics.NonabelianAbelianRecovery.matches_iff_matchesSM,
    ``Physics.NonabelianAbelianRecovery.actualSpectrum_radical]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM Abelian recovery: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM Abelian recovery: layer and {declarations.length} strict axiom checks passed"
