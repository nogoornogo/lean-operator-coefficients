import Physics.StandardModel.Operators.FourWeightLightQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Four-weight light coefficient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.FourWeightLightQque.of_matches,
    ``GUT.FourWeightLightQque.target_iff_of_characters_eq,
    ``GUT.FourWeightLightQque.characters_compatible,
    ``GUT.FourWeightLightQque.common_quotient,
    ``GUT.FourWeightLightQque.exists_qque_coefficient,
    ``GUT.FourWeightLightQque.not_forbidsBothInternalCoefficients,
    ``GUT.NonabelianLightOperators.qque_slots_neutral]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-weight light coefficient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Four-weight light coefficient: layer and {declarations.length} strict axiom checks passed"
