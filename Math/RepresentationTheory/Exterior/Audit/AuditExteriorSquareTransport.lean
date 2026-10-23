import Math.RepresentationTheory.Exterior.ExteriorSquareTransport
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.ExteriorSquareTransport.toLin_conjugate,
    ``Math.ExteriorSquareTransport.compressed_infinitesimal,
    ``Math.ExteriorSquareTransport.infinitesimal_natural,
    ``Math.ExteriorSquareTransport.doubleCommutator_conjugate,
    ``Math.ExteriorSquareTransport.eigenvector_conjugate,
    ``Math.ExteriorSquareTransport.conjugate_refl,
    ``Math.ExteriorSquareTransport.conjugate_trans]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exterior transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exterior transport: {declarations.length} strict axiom checks passed"
