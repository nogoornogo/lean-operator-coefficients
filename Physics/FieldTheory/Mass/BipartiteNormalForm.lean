import Physics.FieldTheory.Mass.Algebra.BipartiteNormalForm
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.BipartiteNormalForm instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BipartiteNormalForm.NoPairings => Physics.BipartiteNormalForm.NoPairings,
  GUT.BipartiteNormalForm.copies_left => Physics.BipartiteNormalForm.copies_left,
  GUT.BipartiteNormalForm.copies_right => Physics.BipartiteNormalForm.copies_right,
  GUT.BipartiteNormalForm.copySlot => Physics.BipartiteNormalForm.copySlot,
  GUT.BipartiteNormalForm.crossMap => Physics.BipartiteNormalForm.crossMap,
  GUT.BipartiteNormalForm.crossMap.congr_simp => Physics.BipartiteNormalForm.crossMap.congr_simp,
  GUT.BipartiteNormalForm.crossMap_evaluation => Physics.BipartiteNormalForm.crossMap_evaluation,
  GUT.BipartiteNormalForm.dualCopiesEquiv => Physics.BipartiteNormalForm.dualCopiesEquiv,
  GUT.BipartiteNormalForm.equiv => Physics.BipartiteNormalForm.equiv,
  GUT.BipartiteNormalForm.form_eq_of_same_side_zero => Physics.BipartiteNormalForm.form_eq_of_same_side_zero,
  GUT.BipartiteNormalForm.normal_form => Physics.BipartiteNormalForm.normal_form,
  GUT.BipartiteNormalForm.of_comp => Physics.BipartiteNormalForm.of_comp,
  GUT.BipartiteNormalForm.prod_left => Physics.BipartiteNormalForm.prod_left,
  GUT.BipartiteNormalForm.prod_right => Physics.BipartiteNormalForm.prod_right
]

assert_compatible GUT.BipartiteNormalForm.NoPairings => Physics.BipartiteNormalForm.NoPairings
assert_compatible GUT.BipartiteNormalForm.copies_left => Physics.BipartiteNormalForm.copies_left
assert_compatible GUT.BipartiteNormalForm.copies_right => Physics.BipartiteNormalForm.copies_right
assert_compatible GUT.BipartiteNormalForm.copySlot => Physics.BipartiteNormalForm.copySlot
assert_compatible GUT.BipartiteNormalForm.crossMap => Physics.BipartiteNormalForm.crossMap
assert_compatible GUT.BipartiteNormalForm.crossMap.congr_simp => Physics.BipartiteNormalForm.crossMap.congr_simp
assert_compatible GUT.BipartiteNormalForm.crossMap_evaluation => Physics.BipartiteNormalForm.crossMap_evaluation
assert_compatible GUT.BipartiteNormalForm.dualCopiesEquiv => Physics.BipartiteNormalForm.dualCopiesEquiv
assert_compatible GUT.BipartiteNormalForm.equiv => Physics.BipartiteNormalForm.equiv
assert_compatible GUT.BipartiteNormalForm.form_eq_of_same_side_zero => Physics.BipartiteNormalForm.form_eq_of_same_side_zero
assert_compatible GUT.BipartiteNormalForm.normal_form => Physics.BipartiteNormalForm.normal_form
assert_compatible GUT.BipartiteNormalForm.of_comp => Physics.BipartiteNormalForm.of_comp
assert_compatible GUT.BipartiteNormalForm.prod_left => Physics.BipartiteNormalForm.prod_left
assert_compatible GUT.BipartiteNormalForm.prod_right => Physics.BipartiteNormalForm.prod_right
