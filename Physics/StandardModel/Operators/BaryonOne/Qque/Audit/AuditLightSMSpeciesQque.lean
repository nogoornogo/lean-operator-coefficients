import Physics.StandardModel.Operators.BaryonOne.Qque.LightSMSpeciesQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Species qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.QqueSpinorExterior.HasModelExterior,
    ``Physics.QqueSpinorExterior.hasModelExterior,
    ``Physics.LightSMSpeciesIndex.HasTarget,
    ``Physics.LightSMSpeciesIndex.common_quotient,
    ``Physics.LightSMSpeciesQque.exists_model_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Species qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Species qque: {declarations.length} strict axiom checks passed"
