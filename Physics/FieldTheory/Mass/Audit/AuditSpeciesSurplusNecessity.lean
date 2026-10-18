import Physics.FieldTheory.Mass.SpeciesSurplusNecessity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    let origin := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf origin || (`GUT.SU6).isPrefixOf origin then
      throwError "Unexpected original unified-model import: {mod}"
  let ds := [``GUT.SpeciesSurplusNecessity.ForbiddenExterior,
    ``GUT.SpeciesSurplusNecessity.no_joint_surplus,
    ``GUT.SpeciesSurplusNecessity.bottleneck,
    ``GUT.SpeciesSurplusNecessity.count_bottleneck,
    ``GUT.SpeciesSurplusNecessity.count_parameter_retain]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Constraint pullback: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Constraint pullback: {ds.length} strict transitive checks passed"
