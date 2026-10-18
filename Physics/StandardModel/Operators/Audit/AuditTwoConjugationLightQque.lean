import Physics.StandardModel.Operators.TwoConjugationLightQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Two-conjugation light coefficient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.TwoConjugationLightQque.characters_compatible,
    ``GUT.TwoConjugationLightQque.down_lepton_character_eq,
    ``GUT.TwoConjugationLightQque.common_quotient,
    ``GUT.TwoConjugationLightQque.common_barFive_quotient,
    ``GUT.TwoConjugationLightQque.exists_qque_coefficient,
    ``GUT.TwoConjugationLightQque.not_forbidsBothInternalCoefficients,
    ``GUT.TwoConjugationLightQque.exists_duql_coefficient,
    ``GUT.TwoConjugationLightQque.both_coefficients_exist]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-conjugation light coefficient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-conjugation light coefficient: layer and {declarations.length} strict axiom checks passed"
