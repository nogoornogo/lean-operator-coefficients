import Physics.FieldTheory.Mass.Algebra.BipartiteNormalForm
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.BipartiteNormalForm.NoPairings,
    ``Physics.BipartiteNormalForm.prod_left,
    ``Physics.BipartiteNormalForm.prod_right,
    ``Physics.BipartiteNormalForm.equiv,
    ``Physics.BipartiteNormalForm.copySlot,
    ``Physics.BipartiteNormalForm.copies_left,
    ``Physics.BipartiteNormalForm.copies_right,
    ``Physics.BipartiteNormalForm.dualCopiesEquiv,
    ``Physics.BipartiteNormalForm.of_comp,
    ``Physics.BipartiteNormalForm.crossMap,
    ``Physics.BipartiteNormalForm.crossMap_evaluation,
    ``Physics.BipartiteNormalForm.form_eq_of_same_side_zero,
    ``Physics.BipartiteNormalForm.normal_form]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"Physics.BipartiteNormalForm: {declarations.length} strict transitive axiom checks passed"
