import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvLocalConjugation
import Physics.StandardModel.Gauge.SMGaugeConjugation
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Physics.StandardModel.Operators.BnvSevenFieldTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvLocalConjugation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvLocalConjugation.chirality => Physics.BnvLocalConjugation.chirality,
  GUT.BnvLocalConjugation.conjugate => Physics.BnvLocalConjugation.conjugate,
  GUT.BnvLocalConjugation.five => Physics.BnvLocalConjugation.five,
  GUT.BnvLocalConjugation.gauge => Physics.BnvLocalConjugation.gauge,
  GUT.BnvLocalConjugation.involutive => Physics.BnvLocalConjugation.involutive,
  GUT.BnvLocalConjugation.localField => Physics.BnvLocalConjugation.localField,
  GUT.BnvLocalConjugation.localScalar => Physics.BnvLocalConjugation.localScalar,
  GUT.BnvLocalConjugation.opposite => Physics.BnvLocalConjugation.opposite,
  GUT.BnvLocalConjugation.oppositeScalar => Physics.BnvLocalConjugation.oppositeScalar,
  GUT.BnvLocalConjugation.opposite_involutive => Physics.BnvLocalConjugation.opposite_involutive,
  GUT.BnvLocalConjugation.scalar => Physics.BnvLocalConjugation.scalar,
  GUT.BnvLocalConjugation.spin_involutive => Physics.BnvLocalConjugation.spin_involutive,
  GUT.BnvLocalConjugation.spin_surjective => Physics.BnvLocalConjugation.spin_surjective,
  GUT.BnvLocalConjugation.surjective => Physics.BnvLocalConjugation.surjective,
  GUT.BnvLocalConjugation.tensor => Physics.BnvLocalConjugation.tensor,
  GUT.BnvLocalConjugation.tensorPullback => Physics.BnvLocalConjugation.tensorPullback
]

assert_compatible GUT.BnvLocalConjugation.chirality => Physics.BnvLocalConjugation.chirality
assert_compatible GUT.BnvLocalConjugation.conjugate => Physics.BnvLocalConjugation.conjugate
assert_compatible GUT.BnvLocalConjugation.five => Physics.BnvLocalConjugation.five
assert_compatible GUT.BnvLocalConjugation.gauge => Physics.BnvLocalConjugation.gauge
assert_compatible GUT.BnvLocalConjugation.involutive => Physics.BnvLocalConjugation.involutive
assert_compatible GUT.BnvLocalConjugation.localField => Physics.BnvLocalConjugation.localField
assert_compatible GUT.BnvLocalConjugation.localScalar => Physics.BnvLocalConjugation.localScalar
assert_compatible GUT.BnvLocalConjugation.opposite => Physics.BnvLocalConjugation.opposite
assert_compatible GUT.BnvLocalConjugation.oppositeScalar => Physics.BnvLocalConjugation.oppositeScalar
assert_compatible GUT.BnvLocalConjugation.opposite_involutive => Physics.BnvLocalConjugation.opposite_involutive
assert_compatible GUT.BnvLocalConjugation.scalar => Physics.BnvLocalConjugation.scalar
assert_compatible GUT.BnvLocalConjugation.spin_involutive => Physics.BnvLocalConjugation.spin_involutive
assert_compatible GUT.BnvLocalConjugation.spin_surjective => Physics.BnvLocalConjugation.spin_surjective
assert_compatible GUT.BnvLocalConjugation.surjective => Physics.BnvLocalConjugation.surjective
assert_compatible GUT.BnvLocalConjugation.tensor => Physics.BnvLocalConjugation.tensor
assert_compatible GUT.BnvLocalConjugation.tensorPullback => Physics.BnvLocalConjugation.tensorPullback
