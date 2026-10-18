import Math.RepresentationTheory.BinaryPatternCoefficient
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Binary exterior audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.BinaryExteriorProduct.ext,
    ``Math.BinaryExteriorProduct.coe_map_tmul, ``Math.BinaryExteriorProduct.injective,
    ``Math.BinaryExteriorProduct.map_pure, ``Math.BinaryPatternExterior.raw_pure,
    ``Math.BinaryPatternExterior.forward_pure, ``Math.BinaryPatternExterior.inclusion_forward,
    ``Math.BinaryPatternExterior.inclusion_injective, ``Math.BinaryPatternExterior.forward_injective,
    ``Math.BinaryPatternExterior.values_reconstruct, ``Math.BinaryPatternExterior.forward_surjective,
    ``Math.BinaryPatternExterior.linearEquiv, ``Math.BinaryPatternExterior.raw_action,
    ``Math.BinaryPatternExterior.equiv, ``Math.BinaryPatternExterior.dimension,
    ``Math.BinaryPatternExterior.character, ``Math.BinaryPatternExterior.character_diagonal,
    ``Math.BinaryPatternCoefficient.withSpectator, ``Math.BinaryPatternCoefficient.equiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Binary exterior audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Binary exterior audit: layer and {ds.length} strict transitive checks passed"
