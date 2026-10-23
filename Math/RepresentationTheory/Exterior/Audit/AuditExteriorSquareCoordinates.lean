import Math.RepresentationTheory.Exterior.ExteriorSquareCoordinates
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.ExteriorSquareCoordinates.basis_apply,
    ``Math.ExteriorSquareCoordinates.matrix_minor,
    ``Math.ExteriorSquareCoordinates.infinitesimal_leibniz,
    ``Math.ExteriorSquareCoordinates.infinitesimal_matrix,
    ``Math.ExteriorSquareCoordinates.hasDerivAt_matrix]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior-square coordinates: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior-square coordinates: {declarations.length} strict axiom checks passed"
