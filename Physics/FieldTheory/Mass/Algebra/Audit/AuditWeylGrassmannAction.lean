import Physics.FieldTheory.Mass.Algebra.WeylGrassmannAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Weyl Grassmann action imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.WeylGrassmannAction.generator_swap,
    ``Physics.WeylGrassmannAction.pair_symmetric,
    ``Physics.WeylGrassmannAction.four_component_right,
    ``Physics.WeylGrassmannAction.three_species_action]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weyl Grassmann action {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weyl Grassmann action: layer and {ds.length} strict transitive checks passed"
