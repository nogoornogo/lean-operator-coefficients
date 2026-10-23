import Physics.StandardModel.Operators.Selection.NonabelianLightOperators
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-Abelian light operators imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.NonabelianLightOperators.exists_qque_coefficient,
    ``Physics.NonabelianLightOperators.exists_duql_coefficient,
    ``Physics.NonabelianLightOperators.qque_slots_neutral,
    ``Physics.NonabelianLightOperators.duql_slots_neutral,
    ``Physics.NonabelianLightOperators.both_coefficients_exist,
    ``Physics.NonabelianLightOperators.not_forbidsBothInternalCoefficients]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-Abelian light operators: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-Abelian light operators: layer and {declarations.length} strict axiom checks passed"
