import Physics.FieldTheory.Mass.Algebra.ExactRadical
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.ExactRadical instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactRadical.exact_iff => Physics.ExactRadical.exact_iff,
  GUT.ExactRadical.family_exists_iff => Physics.ExactRadical.family_exists_iff,
  GUT.ExactRadical.nondegenerate_iff => Physics.ExactRadical.nondegenerate_iff,
  GUT.ExactRadical.quotientForm => Physics.ExactRadical.quotientForm,
  GUT.ExactRadical.quotientForm.congr_simp => Physics.ExactRadical.quotientForm.congr_simp,
  GUT.ExactRadical.quotientForm_mk => Physics.ExactRadical.quotientForm_mk,
  GUT.ExactRadical.quotientForm_symmetric => Physics.ExactRadical.quotientForm_symmetric
]

assert_compatible GUT.ExactRadical.exact_iff => Physics.ExactRadical.exact_iff
assert_compatible GUT.ExactRadical.family_exists_iff => Physics.ExactRadical.family_exists_iff
assert_compatible GUT.ExactRadical.nondegenerate_iff => Physics.ExactRadical.nondegenerate_iff
assert_compatible GUT.ExactRadical.quotientForm => Physics.ExactRadical.quotientForm
assert_compatible GUT.ExactRadical.quotientForm.congr_simp => Physics.ExactRadical.quotientForm.congr_simp
assert_compatible GUT.ExactRadical.quotientForm_mk => Physics.ExactRadical.quotientForm_mk
assert_compatible GUT.ExactRadical.quotientForm_symmetric => Physics.ExactRadical.quotientForm_symmetric
