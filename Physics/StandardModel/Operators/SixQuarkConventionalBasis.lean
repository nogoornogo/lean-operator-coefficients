import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalBasis
import Physics.StandardModel.Operators.SixQuarkTwoCoordinates
import Physics.StandardModel.Operators.DeltaBTwoContractionRelations
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkConventionalBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkConventionalBasis.O1 => Physics.SixQuarkConventionalBasis.O1,
  GUT.SixQuarkConventionalBasis.O2 => Physics.SixQuarkConventionalBasis.O2,
  GUT.SixQuarkConventionalBasis.O3 => Physics.SixQuarkConventionalBasis.O3,
  GUT.SixQuarkConventionalBasis.O3_eq_existing => Physics.SixQuarkConventionalBasis.O3_eq_existing,
  GUT.SixQuarkConventionalBasis.O3_witness => Physics.SixQuarkConventionalBasis.O3_witness,
  GUT.SixQuarkConventionalBasis.colorAAS => Physics.SixQuarkConventionalBasis.colorAAS,
  GUT.SixQuarkConventionalBasis.colorAAS.eq_1 => Physics.SixQuarkConventionalBasis.colorAAS.eq_1,
  GUT.SixQuarkConventionalBasis.colorAAS_invariant => Physics.SixQuarkConventionalBasis.colorAAS_invariant,
  GUT.SixQuarkConventionalBasis.colorSSS => Physics.SixQuarkConventionalBasis.colorSSS,
  GUT.SixQuarkConventionalBasis.colorSSS.eq_1 => Physics.SixQuarkConventionalBasis.colorSSS.eq_1,
  GUT.SixQuarkConventionalBasis.colorSSS_invariant => Physics.SixQuarkConventionalBasis.colorSSS_invariant,
  GUT.SixQuarkConventionalBasis.combine_invariant => Physics.SixQuarkConventionalBasis.combine_invariant,
  GUT.SixQuarkConventionalBasis.descend => Physics.SixQuarkConventionalBasis.descend,
  GUT.SixQuarkConventionalBasis.orderedO1 => Physics.SixQuarkConventionalBasis.orderedO1,
  GUT.SixQuarkConventionalBasis.orderedO1.eq_1 => Physics.SixQuarkConventionalBasis.orderedO1.eq_1,
  GUT.SixQuarkConventionalBasis.orderedO1_apply => Physics.SixQuarkConventionalBasis.orderedO1_apply,
  GUT.SixQuarkConventionalBasis.orderedO1_invariant => Physics.SixQuarkConventionalBasis.orderedO1_invariant,
  GUT.SixQuarkConventionalBasis.orderedO2 => Physics.SixQuarkConventionalBasis.orderedO2,
  GUT.SixQuarkConventionalBasis.orderedO2.eq_1 => Physics.SixQuarkConventionalBasis.orderedO2.eq_1,
  GUT.SixQuarkConventionalBasis.orderedO2_apply => Physics.SixQuarkConventionalBasis.orderedO2_apply,
  GUT.SixQuarkConventionalBasis.orderedO2_invariant => Physics.SixQuarkConventionalBasis.orderedO2_invariant,
  GUT.SixQuarkConventionalBasis.orderedO3 => Physics.SixQuarkConventionalBasis.orderedO3,
  GUT.SixQuarkConventionalBasis.orderedO3.eq_1 => Physics.SixQuarkConventionalBasis.orderedO3.eq_1,
  GUT.SixQuarkConventionalBasis.orderedO3_apply => Physics.SixQuarkConventionalBasis.orderedO3_apply,
  GUT.SixQuarkConventionalBasis.orderedO3_eq_existing => Physics.SixQuarkConventionalBasis.orderedO3_eq_existing,
  GUT.SixQuarkConventionalBasis.orderedO3_invariant => Physics.SixQuarkConventionalBasis.orderedO3_invariant
]

assert_compatible GUT.SixQuarkConventionalBasis.O1 => Physics.SixQuarkConventionalBasis.O1
assert_compatible GUT.SixQuarkConventionalBasis.O2 => Physics.SixQuarkConventionalBasis.O2
assert_compatible GUT.SixQuarkConventionalBasis.O3 => Physics.SixQuarkConventionalBasis.O3
assert_compatible GUT.SixQuarkConventionalBasis.O3_eq_existing => Physics.SixQuarkConventionalBasis.O3_eq_existing
assert_compatible GUT.SixQuarkConventionalBasis.O3_witness => Physics.SixQuarkConventionalBasis.O3_witness
assert_compatible GUT.SixQuarkConventionalBasis.colorAAS => Physics.SixQuarkConventionalBasis.colorAAS
assert_compatible GUT.SixQuarkConventionalBasis.colorAAS.eq_1 => Physics.SixQuarkConventionalBasis.colorAAS.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.colorAAS_invariant => Physics.SixQuarkConventionalBasis.colorAAS_invariant
assert_compatible GUT.SixQuarkConventionalBasis.colorSSS => Physics.SixQuarkConventionalBasis.colorSSS
assert_compatible GUT.SixQuarkConventionalBasis.colorSSS.eq_1 => Physics.SixQuarkConventionalBasis.colorSSS.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.colorSSS_invariant => Physics.SixQuarkConventionalBasis.colorSSS_invariant
assert_compatible GUT.SixQuarkConventionalBasis.combine_invariant => Physics.SixQuarkConventionalBasis.combine_invariant
assert_compatible GUT.SixQuarkConventionalBasis.descend => Physics.SixQuarkConventionalBasis.descend
assert_compatible GUT.SixQuarkConventionalBasis.orderedO1 => Physics.SixQuarkConventionalBasis.orderedO1
assert_compatible GUT.SixQuarkConventionalBasis.orderedO1.eq_1 => Physics.SixQuarkConventionalBasis.orderedO1.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.orderedO1_apply => Physics.SixQuarkConventionalBasis.orderedO1_apply
assert_compatible GUT.SixQuarkConventionalBasis.orderedO1_invariant => Physics.SixQuarkConventionalBasis.orderedO1_invariant
assert_compatible GUT.SixQuarkConventionalBasis.orderedO2 => Physics.SixQuarkConventionalBasis.orderedO2
assert_compatible GUT.SixQuarkConventionalBasis.orderedO2.eq_1 => Physics.SixQuarkConventionalBasis.orderedO2.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.orderedO2_apply => Physics.SixQuarkConventionalBasis.orderedO2_apply
assert_compatible GUT.SixQuarkConventionalBasis.orderedO2_invariant => Physics.SixQuarkConventionalBasis.orderedO2_invariant
assert_compatible GUT.SixQuarkConventionalBasis.orderedO3 => Physics.SixQuarkConventionalBasis.orderedO3
assert_compatible GUT.SixQuarkConventionalBasis.orderedO3.eq_1 => Physics.SixQuarkConventionalBasis.orderedO3.eq_1
assert_compatible GUT.SixQuarkConventionalBasis.orderedO3_apply => Physics.SixQuarkConventionalBasis.orderedO3_apply
assert_compatible GUT.SixQuarkConventionalBasis.orderedO3_eq_existing => Physics.SixQuarkConventionalBasis.orderedO3_eq_existing
assert_compatible GUT.SixQuarkConventionalBasis.orderedO3_invariant => Physics.SixQuarkConventionalBasis.orderedO3_invariant
