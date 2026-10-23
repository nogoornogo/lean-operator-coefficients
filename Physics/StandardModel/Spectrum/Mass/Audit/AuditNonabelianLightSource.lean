import Physics.StandardModel.Spectrum.Mass.NonabelianLightSource
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Non-Abelian light source imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.ResidualLightQuotient.exists_split_of_index_eq,
    ``Physics.ResidualLightQuotient.exists_common_quotient,
    ``Physics.NonabelianLightSource.common_ten_quotient,
    ``Physics.NonabelianLightSource.common_barFive_quotient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-Abelian light source: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Non-Abelian light source: layer and {declarations.length} strict axiom checks passed"
