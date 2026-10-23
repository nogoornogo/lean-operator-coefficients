import Physics.StandardModel.Operators.Support.Coordinates.SMWeylFiniteKernel
import Physics.StandardModel.Operators.QLFiniteSupport
import Physics.FieldTheory.Spinor.WeylRealTransvections
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMWeylFiniteKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMWeylFiniteKernel.Carrier => Physics.SMWeylFiniteKernel.Carrier,
  GUT.SMWeylFiniteKernel.action => Physics.SMWeylFiniteKernel.action,
  GUT.SMWeylFiniteKernel.action_polynomial => Physics.SMWeylFiniteKernel.action_polynomial,
  GUT.SMWeylFiniteKernel.allowed_iff_rank_lt => Physics.SMWeylFiniteKernel.allowed_iff_rank_lt,
  GUT.SMWeylFiniteKernel.basis => Physics.SMWeylFiniteKernel.basis,
  GUT.SMWeylFiniteKernel.boson_fixed => Physics.SMWeylFiniteKernel.boson_fixed,
  GUT.SMWeylFiniteKernel.canonicalEquiv => Physics.SMWeylFiniteKernel.canonicalEquiv,
  GUT.SMWeylFiniteKernel.coefficientEquiv => Physics.SMWeylFiniteKernel.coefficientEquiv,
  GUT.SMWeylFiniteKernel.exhaustive => Physics.SMWeylFiniteKernel.exhaustive,
  GUT.SMWeylFiniteKernel.fieldDirection => Physics.SMWeylFiniteKernel.fieldDirection,
  GUT.SMWeylFiniteKernel.fieldDirection.eq_1 => Physics.SMWeylFiniteKernel.fieldDirection.eq_1,
  GUT.SMWeylFiniteKernel.fieldFinite => Physics.SMWeylFiniteKernel.fieldFinite,
  GUT.SMWeylFiniteKernel.field_affine => Physics.SMWeylFiniteKernel.field_affine,
  GUT.SMWeylFiniteKernel.fullAction => Physics.SMWeylFiniteKernel.fullAction,
  GUT.SMWeylFiniteKernel.inclusion => Physics.SMWeylFiniteKernel.inclusion,
  GUT.SMWeylFiniteKernel.inclusion.eq_1 => Physics.SMWeylFiniteKernel.inclusion.eq_1,
  GUT.SMWeylFiniteKernel.source => Physics.SMWeylFiniteKernel.source,
  GUT.SMWeylFiniteKernel.sourceFinite => Physics.SMWeylFiniteKernel.sourceFinite,
  GUT.SMWeylFiniteKernel.source_polynomial => Physics.SMWeylFiniteKernel.source_polynomial
]

assert_compatible GUT.SMWeylFiniteKernel.Carrier => Physics.SMWeylFiniteKernel.Carrier
assert_compatible GUT.SMWeylFiniteKernel.action => Physics.SMWeylFiniteKernel.action
assert_compatible GUT.SMWeylFiniteKernel.action_polynomial => Physics.SMWeylFiniteKernel.action_polynomial
assert_compatible GUT.SMWeylFiniteKernel.allowed_iff_rank_lt => Physics.SMWeylFiniteKernel.allowed_iff_rank_lt
assert_compatible GUT.SMWeylFiniteKernel.basis => Physics.SMWeylFiniteKernel.basis
assert_compatible GUT.SMWeylFiniteKernel.boson_fixed => Physics.SMWeylFiniteKernel.boson_fixed
assert_compatible GUT.SMWeylFiniteKernel.canonicalEquiv => Physics.SMWeylFiniteKernel.canonicalEquiv
assert_compatible GUT.SMWeylFiniteKernel.coefficientEquiv => Physics.SMWeylFiniteKernel.coefficientEquiv
assert_compatible GUT.SMWeylFiniteKernel.exhaustive => Physics.SMWeylFiniteKernel.exhaustive
assert_compatible GUT.SMWeylFiniteKernel.fieldDirection => Physics.SMWeylFiniteKernel.fieldDirection
assert_compatible GUT.SMWeylFiniteKernel.fieldDirection.eq_1 => Physics.SMWeylFiniteKernel.fieldDirection.eq_1
assert_compatible GUT.SMWeylFiniteKernel.fieldFinite => Physics.SMWeylFiniteKernel.fieldFinite
assert_compatible GUT.SMWeylFiniteKernel.field_affine => Physics.SMWeylFiniteKernel.field_affine
assert_compatible GUT.SMWeylFiniteKernel.fullAction => Physics.SMWeylFiniteKernel.fullAction
assert_compatible GUT.SMWeylFiniteKernel.inclusion => Physics.SMWeylFiniteKernel.inclusion
assert_compatible GUT.SMWeylFiniteKernel.inclusion.eq_1 => Physics.SMWeylFiniteKernel.inclusion.eq_1
assert_compatible GUT.SMWeylFiniteKernel.source => Physics.SMWeylFiniteKernel.source
assert_compatible GUT.SMWeylFiniteKernel.sourceFinite => Physics.SMWeylFiniteKernel.sourceFinite
assert_compatible GUT.SMWeylFiniteKernel.source_polynomial => Physics.SMWeylFiniteKernel.source_polynomial
