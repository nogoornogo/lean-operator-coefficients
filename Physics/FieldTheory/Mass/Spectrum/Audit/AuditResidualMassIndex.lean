import Physics.FieldTheory.Mass.Spectrum.ResidualMassIndex
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Residual mass index imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.ResidualMassIndex.light_torus_unitary,
    ``Physics.ResidualMassIndex.weight_index_invariant]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual mass index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual mass index: layer and {declarations.length} strict axiom checks passed"
