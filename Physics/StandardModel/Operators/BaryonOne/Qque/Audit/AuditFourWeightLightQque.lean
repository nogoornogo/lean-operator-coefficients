import Physics.StandardModel.Operators.BaryonOne.Qque.FourWeightLightQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Four-weight light coefficient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.FourWeightLightQque.of_matches,
    ``Physics.FourWeightLightQque.target_iff_of_characters_eq,
    ``Physics.FourWeightLightQque.characters_compatible,
    ``Physics.FourWeightLightQque.common_quotient,
    ``Physics.FourWeightLightQque.exists_qque_coefficient,
    ``Physics.FourWeightLightQque.not_forbidsBothInternalCoefficients,
    ``Physics.NonabelianLightOperators.qque_slots_neutral]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-weight light coefficient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Four-weight light coefficient: layer and {declarations.length} strict axiom checks passed"
