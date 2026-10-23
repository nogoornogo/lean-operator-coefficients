import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoSixQuark
import Math.RepresentationTheory.SixSlotAlternation
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoSixQuark instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoSixQuark.ColorPair => Physics.DeltaBTwoSixQuark.ColorPair,
  GUT.DeltaBTwoSixQuark.RightQuark => Physics.DeltaBTwoSixQuark.RightQuark,
  GUT.DeltaBTwoSixQuark.Spin => Physics.DeltaBTwoSixQuark.Spin,
  GUT.DeltaBTwoSixQuark.SymmetryGroup => Physics.DeltaBTwoSixQuark.SymmetryGroup,
  GUT.DeltaBTwoSixQuark.colorAAS => Physics.DeltaBTwoSixQuark.colorAAS,
  GUT.DeltaBTwoSixQuark.colorAAS.eq_1 => Physics.DeltaBTwoSixQuark.colorAAS.eq_1,
  GUT.DeltaBTwoSixQuark.colorAASMulti => Physics.DeltaBTwoSixQuark.colorAASMulti,
  GUT.DeltaBTwoSixQuark.colorAASMulti.eq_1 => Physics.DeltaBTwoSixQuark.colorAASMulti.eq_1,
  GUT.DeltaBTwoSixQuark.colorAAS_tmul => Physics.DeltaBTwoSixQuark.colorAAS_tmul,
  GUT.DeltaBTwoSixQuark.diquark => Physics.DeltaBTwoSixQuark.diquark,
  GUT.DeltaBTwoSixQuark.diquark.eq_1 => Physics.DeltaBTwoSixQuark.diquark.eq_1,
  GUT.DeltaBTwoSixQuark.diquark_tmul => Physics.DeltaBTwoSixQuark.diquark_tmul,
  GUT.DeltaBTwoSixQuark.downField => Physics.DeltaBTwoSixQuark.downField,
  GUT.DeltaBTwoSixQuark.downField.eq_1 => Physics.DeltaBTwoSixQuark.downField.eq_1,
  GUT.DeltaBTwoSixQuark.eps2Bilin_self => Physics.DeltaBTwoSixQuark.eps2Bilin_self,
  GUT.DeltaBTwoSixQuark.exteriorCoefficient => Physics.DeltaBTwoSixQuark.exteriorCoefficient,
  GUT.DeltaBTwoSixQuark.exteriorCoefficient.eq_1 => Physics.DeltaBTwoSixQuark.exteriorCoefficient.eq_1,
  GUT.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero => Physics.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero,
  GUT.DeltaBTwoSixQuark.exteriorCoefficient_witness => Physics.DeltaBTwoSixQuark.exteriorCoefficient_witness,
  GUT.DeltaBTwoSixQuark.orderedContraction => Physics.DeltaBTwoSixQuark.orderedContraction,
  GUT.DeltaBTwoSixQuark.orderedContraction.eq_1 => Physics.DeltaBTwoSixQuark.orderedContraction.eq_1,
  GUT.DeltaBTwoSixQuark.orderedContraction_invariant_linear => Physics.DeltaBTwoSixQuark.orderedContraction_invariant_linear,
  GUT.DeltaBTwoSixQuark.orderedContraction_tmul => Physics.DeltaBTwoSixQuark.orderedContraction_tmul,
  GUT.DeltaBTwoSixQuark.orderedIntertwiner => Physics.DeltaBTwoSixQuark.orderedIntertwiner,
  GUT.DeltaBTwoSixQuark.orderedIntertwiner.eq_1 => Physics.DeltaBTwoSixQuark.orderedIntertwiner.eq_1,
  GUT.DeltaBTwoSixQuark.rightBasis => Physics.DeltaBTwoSixQuark.rightBasis,
  GUT.DeltaBTwoSixQuark.rightBasis.eq_1 => Physics.DeltaBTwoSixQuark.rightBasis.eq_1,
  GUT.DeltaBTwoSixQuark.rightEps_invariant => Physics.DeltaBTwoSixQuark.rightEps_invariant,
  GUT.DeltaBTwoSixQuark.sixQuark_phases => Physics.DeltaBTwoSixQuark.sixQuark_phases,
  GUT.DeltaBTwoSixQuark.upField => Physics.DeltaBTwoSixQuark.upField,
  GUT.DeltaBTwoSixQuark.upField.eq_1 => Physics.DeltaBTwoSixQuark.upField.eq_1,
  GUT.DeltaBTwoSixQuark.witness => Physics.DeltaBTwoSixQuark.witness,
  GUT.DeltaBTwoSixQuark.witness.eq_1 => Physics.DeltaBTwoSixQuark.witness.eq_1,
  GUT.DeltaBTwoSixQuark.witness_evaluation => Physics.DeltaBTwoSixQuark.witness_evaluation,
  GUT.DeltaBTwoSixQuark.witness_five => Physics.DeltaBTwoSixQuark.witness_five,
  GUT.DeltaBTwoSixQuark.witness_four => Physics.DeltaBTwoSixQuark.witness_four,
  GUT.DeltaBTwoSixQuark.witness_one => Physics.DeltaBTwoSixQuark.witness_one,
  GUT.DeltaBTwoSixQuark.witness_three => Physics.DeltaBTwoSixQuark.witness_three,
  GUT.DeltaBTwoSixQuark.witness_two => Physics.DeltaBTwoSixQuark.witness_two,
  GUT.DeltaBTwoSixQuark.witness_zero => Physics.DeltaBTwoSixQuark.witness_zero,
  GUT.SMEpsilonTensor.weakTensor.eq_1 => Physics.SMEpsilonTensor.weakTensor.eq_1
]

assert_compatible GUT.DeltaBTwoSixQuark.ColorPair => Physics.DeltaBTwoSixQuark.ColorPair
assert_compatible GUT.DeltaBTwoSixQuark.RightQuark => Physics.DeltaBTwoSixQuark.RightQuark
assert_compatible GUT.DeltaBTwoSixQuark.Spin => Physics.DeltaBTwoSixQuark.Spin
assert_compatible GUT.DeltaBTwoSixQuark.SymmetryGroup => Physics.DeltaBTwoSixQuark.SymmetryGroup
assert_compatible GUT.DeltaBTwoSixQuark.colorAAS => Physics.DeltaBTwoSixQuark.colorAAS
assert_compatible GUT.DeltaBTwoSixQuark.colorAAS.eq_1 => Physics.DeltaBTwoSixQuark.colorAAS.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.colorAASMulti => Physics.DeltaBTwoSixQuark.colorAASMulti
assert_compatible GUT.DeltaBTwoSixQuark.colorAASMulti.eq_1 => Physics.DeltaBTwoSixQuark.colorAASMulti.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.colorAAS_tmul => Physics.DeltaBTwoSixQuark.colorAAS_tmul
assert_compatible GUT.DeltaBTwoSixQuark.diquark => Physics.DeltaBTwoSixQuark.diquark
assert_compatible GUT.DeltaBTwoSixQuark.diquark.eq_1 => Physics.DeltaBTwoSixQuark.diquark.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.diquark_tmul => Physics.DeltaBTwoSixQuark.diquark_tmul
assert_compatible GUT.DeltaBTwoSixQuark.downField => Physics.DeltaBTwoSixQuark.downField
assert_compatible GUT.DeltaBTwoSixQuark.downField.eq_1 => Physics.DeltaBTwoSixQuark.downField.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.eps2Bilin_self => Physics.DeltaBTwoSixQuark.eps2Bilin_self
assert_compatible GUT.DeltaBTwoSixQuark.exteriorCoefficient => Physics.DeltaBTwoSixQuark.exteriorCoefficient
assert_compatible GUT.DeltaBTwoSixQuark.exteriorCoefficient.eq_1 => Physics.DeltaBTwoSixQuark.exteriorCoefficient.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero => Physics.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero
assert_compatible GUT.DeltaBTwoSixQuark.exteriorCoefficient_witness => Physics.DeltaBTwoSixQuark.exteriorCoefficient_witness
assert_compatible GUT.DeltaBTwoSixQuark.orderedContraction => Physics.DeltaBTwoSixQuark.orderedContraction
assert_compatible GUT.DeltaBTwoSixQuark.orderedContraction.eq_1 => Physics.DeltaBTwoSixQuark.orderedContraction.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.orderedContraction_invariant_linear => Physics.DeltaBTwoSixQuark.orderedContraction_invariant_linear
assert_compatible GUT.DeltaBTwoSixQuark.orderedContraction_tmul => Physics.DeltaBTwoSixQuark.orderedContraction_tmul
assert_compatible GUT.DeltaBTwoSixQuark.orderedIntertwiner => Physics.DeltaBTwoSixQuark.orderedIntertwiner
assert_compatible GUT.DeltaBTwoSixQuark.orderedIntertwiner.eq_1 => Physics.DeltaBTwoSixQuark.orderedIntertwiner.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.rightBasis => Physics.DeltaBTwoSixQuark.rightBasis
assert_compatible GUT.DeltaBTwoSixQuark.rightBasis.eq_1 => Physics.DeltaBTwoSixQuark.rightBasis.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.rightEps_invariant => Physics.DeltaBTwoSixQuark.rightEps_invariant
assert_compatible GUT.DeltaBTwoSixQuark.sixQuark_phases => Physics.DeltaBTwoSixQuark.sixQuark_phases
assert_compatible GUT.DeltaBTwoSixQuark.upField => Physics.DeltaBTwoSixQuark.upField
assert_compatible GUT.DeltaBTwoSixQuark.upField.eq_1 => Physics.DeltaBTwoSixQuark.upField.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.witness => Physics.DeltaBTwoSixQuark.witness
assert_compatible GUT.DeltaBTwoSixQuark.witness.eq_1 => Physics.DeltaBTwoSixQuark.witness.eq_1
assert_compatible GUT.DeltaBTwoSixQuark.witness_evaluation => Physics.DeltaBTwoSixQuark.witness_evaluation
assert_compatible GUT.DeltaBTwoSixQuark.witness_five => Physics.DeltaBTwoSixQuark.witness_five
assert_compatible GUT.DeltaBTwoSixQuark.witness_four => Physics.DeltaBTwoSixQuark.witness_four
assert_compatible GUT.DeltaBTwoSixQuark.witness_one => Physics.DeltaBTwoSixQuark.witness_one
assert_compatible GUT.DeltaBTwoSixQuark.witness_three => Physics.DeltaBTwoSixQuark.witness_three
assert_compatible GUT.DeltaBTwoSixQuark.witness_two => Physics.DeltaBTwoSixQuark.witness_two
assert_compatible GUT.DeltaBTwoSixQuark.witness_zero => Physics.DeltaBTwoSixQuark.witness_zero
assert_compatible GUT.SMEpsilonTensor.weakTensor.eq_1 => Physics.SMEpsilonTensor.weakTensor.eq_1
