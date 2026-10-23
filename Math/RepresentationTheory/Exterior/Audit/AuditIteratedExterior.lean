import Math.RepresentationTheory.Exterior.ExteriorContentTree
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Iterated exterior audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SumPatternExterior.raw_injective, ``Math.SumPatternExterior.raw_pure,
    ``Math.SumPatternExterior.tensor_ext, ``Math.SumPatternExterior.forward_pure,
    ``Math.SumPatternExterior.inclusion_forward, ``Math.SumPatternExterior.forward_injective,
    ``Math.SumPatternExterior.values_reconstruct, ``Math.SumPatternExterior.forward_surjective,
    ``Math.SumPatternExterior.linearEquiv, ``Math.SumPatternExterior.values_action,
    ``Math.SumPatternExterior.equiv, ``Math.ExteriorContentTree.nodeTransport,
    ``Math.ExteriorContentTree.decomposition, ``Math.ExteriorContentTree.carrier_finite,
    ``Math.ExteriorContentTree.carrier_dimension, ``Math.ExteriorContentTree.source_dimension,
    ``Math.ExteriorContentTree.withSpectator, ``Math.ExteriorContentTree.coefficientEquiv,
    ``Math.ExteriorContentTree.factor_character, ``Math.ExteriorContentTree.source_character]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Iterated exterior audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Iterated exterior audit: layer and {ds.length} strict transitive checks passed"
