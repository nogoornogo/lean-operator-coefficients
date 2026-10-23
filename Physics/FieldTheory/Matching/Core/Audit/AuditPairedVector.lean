import Physics.FieldTheory.Matching.Core.PairedVector
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.PairedVector.pairing_rankOne,
    ``Physics.PairedVector.pairing_symmetric,
    ``Physics.PairedVector.pairing_nondegenerate,
    ``Physics.PairedVector.eliminate]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Tree matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Tree matching: {declarations.length} strict axiom checks passed"
