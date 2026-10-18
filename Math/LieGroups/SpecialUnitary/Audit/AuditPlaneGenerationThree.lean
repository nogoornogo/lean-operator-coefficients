import Math.LieGroups.SpecialUnitary.PlaneGenerationThree
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "SU3 plane generation imports application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SU3PlaneGeneration.matrix01_mem,
    ``Math.SU3PlaneGeneration.matrix02_mem,
    ``Math.SU3PlaneGeneration.rotation01_plane,
    ``Math.SU3PlaneGeneration.rotation02_plane,
    ``Math.SU3PlaneGeneration.eliminate_pair,
    ``Math.SU3PlaneGeneration.column_norm,
    ``Math.SU3PlaneGeneration.reduce_first_column,
    ``Math.SU3PlaneGeneration.row_fixed,
    ``Math.SU3PlaneGeneration.tail_mem,
    ``Math.SU3PlaneGeneration.inverse_plane,
    ``Math.SU3PlaneGeneration.three_plane_decomposition,
    ``Math.SU3PlaneGeneration.closure_planes,
    ``Math.SU3PlaneGeneration.generates,
    ``Math.SU3PlaneGeneration.invariant_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU3 plane generation: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU3 plane generation: layer and {ds.length} strict transitive axiom checks passed"
