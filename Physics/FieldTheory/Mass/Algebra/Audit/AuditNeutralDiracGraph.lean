import Physics.FieldTheory.Mass.Algebra.NeutralDiracGraph
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Neutral Dirac graph imports model {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.NeutralDiracGraph.kernel_iff,
    ``Physics.NeutralDiracGraph.mass_symmetric,
    ``Physics.NeutralDiracGraph.light_mem,
    ``Physics.NeutralDiracGraph.light_coordinates,
    ``Physics.NeutralDiracGraph.restrict_zero_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Neutral Dirac graph {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Neutral Dirac graph: layer and {ds.length} strict transitive checks passed"
