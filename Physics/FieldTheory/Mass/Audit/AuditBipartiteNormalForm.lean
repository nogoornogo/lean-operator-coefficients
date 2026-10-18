import Physics.FieldTheory.Mass.BipartiteNormalForm
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.BipartiteNormalForm.NoPairings,
    ``GUT.BipartiteNormalForm.prod_left,
    ``GUT.BipartiteNormalForm.prod_right,
    ``GUT.BipartiteNormalForm.equiv,
    ``GUT.BipartiteNormalForm.copySlot,
    ``GUT.BipartiteNormalForm.copies_left,
    ``GUT.BipartiteNormalForm.copies_right,
    ``GUT.BipartiteNormalForm.dualCopiesEquiv,
    ``GUT.BipartiteNormalForm.of_comp,
    ``GUT.BipartiteNormalForm.crossMap,
    ``GUT.BipartiteNormalForm.crossMap_evaluation,
    ``GUT.BipartiteNormalForm.form_eq_of_same_side_zero,
    ``GUT.BipartiteNormalForm.normal_form]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.BipartiteNormalForm: {declarations.length} strict transitive axiom checks passed"
