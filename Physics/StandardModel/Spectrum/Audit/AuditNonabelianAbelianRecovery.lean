import Physics.StandardModel.Spectrum.NonabelianAbelianRecovery
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM Abelian recovery imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.NonabelianAbelianRecovery.keyCharacter_joint,
    ``GUT.NonabelianAbelianRecovery.actualSpectrum_apply,
    ``GUT.NonabelianAbelianRecovery.actualSpectrum_neg_apply,
    ``GUT.NonabelianAbelianRecovery.targetProfiles_apply,
    ``GUT.NonabelianAbelianRecovery.speciesProfile_total,
    ``GUT.NonabelianAbelianRecovery.speciesProfile_positive_iff,
    ``GUT.NonabelianAbelianRecovery.matches_iff_matchesSM,
    ``GUT.NonabelianAbelianRecovery.actualSpectrum_radical]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM Abelian recovery: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM Abelian recovery: layer and {declarations.length} strict axiom checks passed"
