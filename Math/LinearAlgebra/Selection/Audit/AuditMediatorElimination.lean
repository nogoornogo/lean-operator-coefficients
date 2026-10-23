import Math.LinearAlgebra.Constructions.PairedQuadraticElimination
import Math.LinearAlgebra.Constructions.DiagonalAdjointMass
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.PairedQuadraticElimination.shifted_action,
    ``Math.PairedQuadraticElimination.on_shell,
    ``Math.PairedQuadraticElimination.stationary_variation,
    ``Math.PairedQuadraticElimination.source_equation,
    ``Math.DiagonalAdjointMass.entry,
    ``Math.DiagonalAdjointMass.single_eigenvector,
    ``Math.DiagonalAdjointMass.diagonal_kernel]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Tree matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Tree matching: {declarations.length} strict axiom checks passed"
