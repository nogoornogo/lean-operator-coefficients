import Math.RepresentationTheory.Invariants.MultilinearInvariantHom
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.MultilinearInvariantHom.tensorRepresentation_tprod,
    ``Math.MultilinearInvariantHom.equiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Multilinear Hom audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Multilinear Hom audit: {declarations.length} strict checks passed"
