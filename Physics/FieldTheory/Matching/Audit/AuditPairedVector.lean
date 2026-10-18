import Physics.FieldTheory.Matching.PairedVector
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.PairedVector.pairing_rankOne,
    ``GUT.PairedVector.pairing_symmetric,
    ``GUT.PairedVector.pairing_nondegenerate,
    ``GUT.PairedVector.eliminate]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Tree matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Tree matching: {declarations.length} strict axiom checks passed"
