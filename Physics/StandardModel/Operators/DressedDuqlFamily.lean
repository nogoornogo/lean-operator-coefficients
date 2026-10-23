import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DressedDuqlFamily
import Physics.StandardModel.Operators.NeutralHiggsPowers
import Physics.StandardModel.Operators.InverseCyclicSMCharges
import Physics.StandardModel.Operators.ComposableBLSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DressedDuqlFamily instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DressedDuqlFamily.Family => Physics.DressedDuqlFamily.Family,
  GUT.DressedDuqlFamily.Indices => Physics.DressedDuqlFamily.Indices,
  GUT.DressedDuqlFamily.allowed_iff => Physics.DressedDuqlFamily.allowed_iff,
  GUT.DressedDuqlFamily.dictionary => Physics.DressedDuqlFamily.dictionary,
  GUT.DressedDuqlFamily.dictionary_def => Physics.DressedDuqlFamily.dictionary_def,
  GUT.DressedDuqlFamily.dress => Physics.DressedDuqlFamily.dress,
  GUT.DressedDuqlFamily.dress_nonzero => Physics.DressedDuqlFamily.dress_nonzero,
  GUT.DressedDuqlFamily.family_grades => Physics.DressedDuqlFamily.family_grades,
  GUT.DressedDuqlFamily.flavor => Physics.DressedDuqlFamily.flavor,
  GUT.DressedDuqlFamily.forbidden_iff => Physics.DressedDuqlFamily.forbidden_iff,
  GUT.DressedDuqlFamily.indices_nonempty_iff => Physics.DressedDuqlFamily.indices_nonempty_iff,
  GUT.DressedDuqlFamily.seed => Physics.DressedDuqlFamily.seed,
  GUT.DressedDuqlFamily.seed.eq_1 => Physics.DressedDuqlFamily.seed.eq_1,
  GUT.DressedDuqlFamily.seed_dictionary => Physics.DressedDuqlFamily.seed_dictionary,
  GUT.DressedDuqlFamily.seed_injective => Physics.DressedDuqlFamily.seed_injective,
  GUT.DressedDuqlFamily.unbounded_allowance => Physics.DressedDuqlFamily.unbounded_allowance
]

assert_compatible GUT.DressedDuqlFamily.Family => Physics.DressedDuqlFamily.Family
assert_compatible GUT.DressedDuqlFamily.Indices => Physics.DressedDuqlFamily.Indices
assert_compatible GUT.DressedDuqlFamily.allowed_iff => Physics.DressedDuqlFamily.allowed_iff
assert_compatible GUT.DressedDuqlFamily.dictionary => Physics.DressedDuqlFamily.dictionary
assert_compatible GUT.DressedDuqlFamily.dictionary_def => Physics.DressedDuqlFamily.dictionary_def
assert_compatible GUT.DressedDuqlFamily.dress => Physics.DressedDuqlFamily.dress
assert_compatible GUT.DressedDuqlFamily.dress_nonzero => Physics.DressedDuqlFamily.dress_nonzero
assert_compatible GUT.DressedDuqlFamily.family_grades => Physics.DressedDuqlFamily.family_grades
assert_compatible GUT.DressedDuqlFamily.flavor => Physics.DressedDuqlFamily.flavor
assert_compatible GUT.DressedDuqlFamily.forbidden_iff => Physics.DressedDuqlFamily.forbidden_iff
assert_compatible GUT.DressedDuqlFamily.indices_nonempty_iff => Physics.DressedDuqlFamily.indices_nonempty_iff
assert_compatible GUT.DressedDuqlFamily.seed => Physics.DressedDuqlFamily.seed
assert_compatible GUT.DressedDuqlFamily.seed.eq_1 => Physics.DressedDuqlFamily.seed.eq_1
assert_compatible GUT.DressedDuqlFamily.seed_dictionary => Physics.DressedDuqlFamily.seed_dictionary
assert_compatible GUT.DressedDuqlFamily.seed_injective => Physics.DressedDuqlFamily.seed_injective
assert_compatible GUT.DressedDuqlFamily.unbounded_allowance => Physics.DressedDuqlFamily.unbounded_allowance
