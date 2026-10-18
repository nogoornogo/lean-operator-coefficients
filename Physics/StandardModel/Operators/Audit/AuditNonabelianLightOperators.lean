import Physics.StandardModel.Operators.NonabelianLightOperators
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-Abelian light operators imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.NonabelianLightOperators.exists_qque_coefficient,
    ``GUT.NonabelianLightOperators.exists_duql_coefficient,
    ``GUT.NonabelianLightOperators.qque_slots_neutral,
    ``GUT.NonabelianLightOperators.duql_slots_neutral,
    ``GUT.NonabelianLightOperators.both_coefficients_exist,
    ``GUT.NonabelianLightOperators.not_forbidsBothInternalCoefficients]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-Abelian light operators: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-Abelian light operators: layer and {declarations.length} strict axiom checks passed"
