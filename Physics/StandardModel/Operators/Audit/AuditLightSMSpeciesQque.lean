import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Species qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.QqueSpinorExterior.HasModelExterior,
    ``GUT.QqueSpinorExterior.hasModelExterior,
    ``GUT.LightSMSpeciesIndex.HasTarget,
    ``GUT.LightSMSpeciesIndex.common_quotient,
    ``GUT.LightSMSpeciesQque.exists_model_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Species qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Species qque: {declarations.length} strict axiom checks passed"
