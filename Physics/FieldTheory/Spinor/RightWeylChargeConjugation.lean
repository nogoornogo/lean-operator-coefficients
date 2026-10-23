import Physics.FieldTheory.Spinor.Weyl.RightWeylChargeConjugation
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.RightWeylChargeConjugation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.RightWeylChargeConjugation.Dirac => Physics.RightWeylChargeConjugation.Dirac,
  GUT.RightWeylChargeConjugation.charge => Physics.RightWeylChargeConjugation.charge,
  GUT.RightWeylChargeConjugation.charge.eq_1 => Physics.RightWeylChargeConjugation.charge.eq_1,
  GUT.RightWeylChargeConjugation.charge_conjTranspose => Physics.RightWeylChargeConjugation.charge_conjTranspose,
  GUT.RightWeylChargeConjugation.charge_eq => Physics.RightWeylChargeConjugation.charge_eq,
  GUT.RightWeylChargeConjugation.charge_gamma => Physics.RightWeylChargeConjugation.charge_gamma,
  GUT.RightWeylChargeConjugation.charge_transpose => Physics.RightWeylChargeConjugation.charge_transpose,
  GUT.RightWeylChargeConjugation.chirality => Physics.RightWeylChargeConjugation.chirality,
  GUT.RightWeylChargeConjugation.chirality.eq_1 => Physics.RightWeylChargeConjugation.chirality.eq_1,
  GUT.RightWeylChargeConjugation.chirality_orientation => Physics.RightWeylChargeConjugation.chirality_orientation,
  GUT.RightWeylChargeConjugation.diquark => Physics.RightWeylChargeConjugation.diquark,
  GUT.RightWeylChargeConjugation.diquark.eq_1 => Physics.RightWeylChargeConjugation.diquark.eq_1,
  GUT.RightWeylChargeConjugation.embedRight => Physics.RightWeylChargeConjugation.embedRight,
  GUT.RightWeylChargeConjugation.embedRight.eq_1 => Physics.RightWeylChargeConjugation.embedRight.eq_1,
  GUT.RightWeylChargeConjugation.gamma => Physics.RightWeylChargeConjugation.gamma,
  GUT.RightWeylChargeConjugation.gamma.eq_1 => Physics.RightWeylChargeConjugation.gamma.eq_1,
  GUT.RightWeylChargeConjugation.gammaFour => Physics.RightWeylChargeConjugation.gammaFour,
  GUT.RightWeylChargeConjugation.gammaFour.eq_1 => Physics.RightWeylChargeConjugation.gammaFour.eq_1,
  GUT.RightWeylChargeConjugation.gammaOne => Physics.RightWeylChargeConjugation.gammaOne,
  GUT.RightWeylChargeConjugation.gammaOne.eq_1 => Physics.RightWeylChargeConjugation.gammaOne.eq_1,
  GUT.RightWeylChargeConjugation.gammaThree => Physics.RightWeylChargeConjugation.gammaThree,
  GUT.RightWeylChargeConjugation.gammaThree.eq_1 => Physics.RightWeylChargeConjugation.gammaThree.eq_1,
  GUT.RightWeylChargeConjugation.gammaTwo => Physics.RightWeylChargeConjugation.gammaTwo,
  GUT.RightWeylChargeConjugation.gammaTwo.eq_1 => Physics.RightWeylChargeConjugation.gammaTwo.eq_1,
  GUT.RightWeylChargeConjugation.gamma_clifford => Physics.RightWeylChargeConjugation.gamma_clifford,
  GUT.RightWeylChargeConjugation.gamma_hermitian => Physics.RightWeylChargeConjugation.gamma_hermitian,
  GUT.RightWeylChargeConjugation.projector_embedRight => Physics.RightWeylChargeConjugation.projector_embedRight,
  GUT.RightWeylChargeConjugation.projector_eq => Physics.RightWeylChargeConjugation.projector_eq,
  GUT.RightWeylChargeConjugation.projector_idempotent => Physics.RightWeylChargeConjugation.projector_idempotent,
  GUT.RightWeylChargeConjugation.rightProjector => Physics.RightWeylChargeConjugation.rightProjector,
  GUT.RightWeylChargeConjugation.rightProjector.eq_1 => Physics.RightWeylChargeConjugation.rightProjector.eq_1,
  GUT.RightWeylChargeConjugation.right_diquark => Physics.RightWeylChargeConjugation.right_diquark,
  GUT.RightWeylChargeConjugation.three_right_diquarks => Physics.RightWeylChargeConjugation.three_right_diquarks
]

assert_compatible GUT.RightWeylChargeConjugation.Dirac => Physics.RightWeylChargeConjugation.Dirac
assert_compatible GUT.RightWeylChargeConjugation.charge => Physics.RightWeylChargeConjugation.charge
assert_compatible GUT.RightWeylChargeConjugation.charge.eq_1 => Physics.RightWeylChargeConjugation.charge.eq_1
assert_compatible GUT.RightWeylChargeConjugation.charge_conjTranspose => Physics.RightWeylChargeConjugation.charge_conjTranspose
assert_compatible GUT.RightWeylChargeConjugation.charge_eq => Physics.RightWeylChargeConjugation.charge_eq
assert_compatible GUT.RightWeylChargeConjugation.charge_gamma => Physics.RightWeylChargeConjugation.charge_gamma
assert_compatible GUT.RightWeylChargeConjugation.charge_transpose => Physics.RightWeylChargeConjugation.charge_transpose
assert_compatible GUT.RightWeylChargeConjugation.chirality => Physics.RightWeylChargeConjugation.chirality
assert_compatible GUT.RightWeylChargeConjugation.chirality.eq_1 => Physics.RightWeylChargeConjugation.chirality.eq_1
assert_compatible GUT.RightWeylChargeConjugation.chirality_orientation => Physics.RightWeylChargeConjugation.chirality_orientation
assert_compatible GUT.RightWeylChargeConjugation.diquark => Physics.RightWeylChargeConjugation.diquark
assert_compatible GUT.RightWeylChargeConjugation.diquark.eq_1 => Physics.RightWeylChargeConjugation.diquark.eq_1
assert_compatible GUT.RightWeylChargeConjugation.embedRight => Physics.RightWeylChargeConjugation.embedRight
assert_compatible GUT.RightWeylChargeConjugation.embedRight.eq_1 => Physics.RightWeylChargeConjugation.embedRight.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gamma => Physics.RightWeylChargeConjugation.gamma
assert_compatible GUT.RightWeylChargeConjugation.gamma.eq_1 => Physics.RightWeylChargeConjugation.gamma.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gammaFour => Physics.RightWeylChargeConjugation.gammaFour
assert_compatible GUT.RightWeylChargeConjugation.gammaFour.eq_1 => Physics.RightWeylChargeConjugation.gammaFour.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gammaOne => Physics.RightWeylChargeConjugation.gammaOne
assert_compatible GUT.RightWeylChargeConjugation.gammaOne.eq_1 => Physics.RightWeylChargeConjugation.gammaOne.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gammaThree => Physics.RightWeylChargeConjugation.gammaThree
assert_compatible GUT.RightWeylChargeConjugation.gammaThree.eq_1 => Physics.RightWeylChargeConjugation.gammaThree.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gammaTwo => Physics.RightWeylChargeConjugation.gammaTwo
assert_compatible GUT.RightWeylChargeConjugation.gammaTwo.eq_1 => Physics.RightWeylChargeConjugation.gammaTwo.eq_1
assert_compatible GUT.RightWeylChargeConjugation.gamma_clifford => Physics.RightWeylChargeConjugation.gamma_clifford
assert_compatible GUT.RightWeylChargeConjugation.gamma_hermitian => Physics.RightWeylChargeConjugation.gamma_hermitian
assert_compatible GUT.RightWeylChargeConjugation.projector_embedRight => Physics.RightWeylChargeConjugation.projector_embedRight
assert_compatible GUT.RightWeylChargeConjugation.projector_eq => Physics.RightWeylChargeConjugation.projector_eq
assert_compatible GUT.RightWeylChargeConjugation.projector_idempotent => Physics.RightWeylChargeConjugation.projector_idempotent
assert_compatible GUT.RightWeylChargeConjugation.rightProjector => Physics.RightWeylChargeConjugation.rightProjector
assert_compatible GUT.RightWeylChargeConjugation.rightProjector.eq_1 => Physics.RightWeylChargeConjugation.rightProjector.eq_1
assert_compatible GUT.RightWeylChargeConjugation.right_diquark => Physics.RightWeylChargeConjugation.right_diquark
assert_compatible GUT.RightWeylChargeConjugation.three_right_diquarks => Physics.RightWeylChargeConjugation.three_right_diquarks
