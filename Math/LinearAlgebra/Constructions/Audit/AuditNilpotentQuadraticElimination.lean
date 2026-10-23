import Math.LinearAlgebra.Constructions.NilpotentQuadraticElimination
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "NilpotentQuadraticElimination imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.NilpotentQuadraticElimination.inverse,
    ``Math.NilpotentQuadraticElimination.inverse_left,
    ``Math.NilpotentQuadraticElimination.inverse_right,
    ``Math.NilpotentQuadraticElimination.solution,
    ``Math.NilpotentQuadraticElimination.source_equation,
    ``Math.NilpotentQuadraticElimination.unique,
    ``Math.NilpotentQuadraticElimination.action,
    ``Math.NilpotentQuadraticElimination.Stationary,
    ``Math.NilpotentQuadraticElimination.shifted_action,
    ``Math.NilpotentQuadraticElimination.on_shell,
    ``Math.NilpotentQuadraticElimination.solution_stationary,
    ``Math.NilpotentQuadraticElimination.stationary_unique,
    ``Math.NilpotentQuadraticElimination.eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "NilpotentQuadraticElimination: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"NilpotentQuadraticElimination: {ds.length} strict transitive checks passed"
