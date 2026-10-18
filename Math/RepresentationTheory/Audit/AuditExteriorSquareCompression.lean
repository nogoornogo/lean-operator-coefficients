import Math.RepresentationTheory.ExteriorSquareCompression
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.ExteriorSquareCoordinates.compress_infinitesimal,
    ``Math.ExteriorSquareCoordinates.infinitesimal_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior compression: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior compression: {declarations.length} strict axiom checks passed"
