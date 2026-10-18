import Math.RepresentationTheory.ConstantPatternExterior
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Constant content audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ConstantPatternExterior.forward_pure,
    ``Math.ConstantPatternExterior.backward_pure,
    ``Math.ConstantPatternExterior.backward_forward,
    ``Math.ConstantPatternExterior.forward_backward,
    ``Math.ConstantPatternExterior.equiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Constant content audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Constant content audit: layer and {ds.length} strict transitive checks passed"
