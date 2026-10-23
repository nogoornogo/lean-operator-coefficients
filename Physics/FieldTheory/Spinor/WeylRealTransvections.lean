import Physics.FieldTheory.Spinor.Weyl.WeylRealTransvections
import Physics.FieldTheory.Spinor.WeylGeneratorTests
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.RepresentationTheory.AffineStatisticalSampling
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylRealTransvections instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylRealTransvections.Index => Physics.WeylRealTransvections.Index,
  GUT.WeylRealTransvections.Pair => Physics.WeylRealTransvections.Pair,
  GUT.WeylRealTransvections.card_index => Physics.WeylRealTransvections.card_index,
  GUT.WeylRealTransvections.card_tests => Physics.WeylRealTransvections.card_tests,
  GUT.WeylRealTransvections.direction => Physics.WeylRealTransvections.direction,
  GUT.WeylRealTransvections.direction.eq_1 => Physics.WeylRealTransvections.direction.eq_1,
  GUT.WeylRealTransvections.exhaustive => Physics.WeylRealTransvections.exhaustive,
  GUT.WeylRealTransvections.family => Physics.WeylRealTransvections.family,
  GUT.WeylRealTransvections.family.eq_1 => Physics.WeylRealTransvections.family.eq_1,
  GUT.WeylRealTransvections.generates => Physics.WeylRealTransvections.generates,
  GUT.WeylRealTransvections.phase => Physics.WeylRealTransvections.phase,
  GUT.WeylRealTransvections.phase.eq_1 => Physics.WeylRealTransvections.phase.eq_1,
  GUT.WeylRealTransvections.spinor_affine => Physics.WeylRealTransvections.spinor_affine,
  GUT.WeylRealTransvections.split_transvection => Physics.WeylRealTransvections.split_transvection,
  GUT.WeylRealTransvections.tests => Physics.WeylRealTransvections.tests
]

assert_compatible GUT.WeylRealTransvections.Index => Physics.WeylRealTransvections.Index
assert_compatible GUT.WeylRealTransvections.Pair => Physics.WeylRealTransvections.Pair
assert_compatible GUT.WeylRealTransvections.card_index => Physics.WeylRealTransvections.card_index
assert_compatible GUT.WeylRealTransvections.card_tests => Physics.WeylRealTransvections.card_tests
assert_compatible GUT.WeylRealTransvections.direction => Physics.WeylRealTransvections.direction
assert_compatible GUT.WeylRealTransvections.direction.eq_1 => Physics.WeylRealTransvections.direction.eq_1
assert_compatible GUT.WeylRealTransvections.exhaustive => Physics.WeylRealTransvections.exhaustive
assert_compatible GUT.WeylRealTransvections.family => Physics.WeylRealTransvections.family
assert_compatible GUT.WeylRealTransvections.family.eq_1 => Physics.WeylRealTransvections.family.eq_1
assert_compatible GUT.WeylRealTransvections.generates => Physics.WeylRealTransvections.generates
assert_compatible GUT.WeylRealTransvections.phase => Physics.WeylRealTransvections.phase
assert_compatible GUT.WeylRealTransvections.phase.eq_1 => Physics.WeylRealTransvections.phase.eq_1
assert_compatible GUT.WeylRealTransvections.spinor_affine => Physics.WeylRealTransvections.spinor_affine
assert_compatible GUT.WeylRealTransvections.split_transvection => Physics.WeylRealTransvections.split_transvection
assert_compatible GUT.WeylRealTransvections.tests => Physics.WeylRealTransvections.tests
