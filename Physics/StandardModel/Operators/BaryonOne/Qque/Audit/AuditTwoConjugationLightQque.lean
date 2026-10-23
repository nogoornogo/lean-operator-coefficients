import Physics.StandardModel.Operators.BaryonOne.Qque.TwoConjugationLightQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Two-conjugation light coefficient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.TwoConjugationLightQque.characters_compatible,
    ``Physics.TwoConjugationLightQque.down_lepton_character_eq,
    ``Physics.TwoConjugationLightQque.common_quotient,
    ``Physics.TwoConjugationLightQque.common_barFive_quotient,
    ``Physics.TwoConjugationLightQque.exists_qque_coefficient,
    ``Physics.TwoConjugationLightQque.not_forbidsBothInternalCoefficients,
    ``Physics.TwoConjugationLightQque.exists_duql_coefficient,
    ``Physics.TwoConjugationLightQque.both_coefficients_exist]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-conjugation light coefficient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-conjugation light coefficient: layer and {declarations.length} strict axiom checks passed"
