import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar
import Physics.FieldTheory.Jets.ScalarDerivativeInterface
import Physics.FieldTheory.Jets.ScalarFirstVariation
import Physics.FieldTheory.Jets.LagrangianHelper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DerivativeLiteratureScalar.T => Physics.DerivativeLiteratureScalar.T,
  GUT.DerivativeLiteratureScalar.direct_helper_inverse => Physics.DerivativeLiteratureScalar.direct_helper_inverse,
  GUT.DerivativeLiteratureScalar.extraction_agrees => Physics.DerivativeLiteratureScalar.extraction_agrees,
  GUT.DerivativeLiteratureScalar.fourDerivative => Physics.DerivativeLiteratureScalar.fourDerivative,
  GUT.DerivativeLiteratureScalar.fourDerivative.eq_1 => Physics.DerivativeLiteratureScalar.fourDerivative.eq_1,
  GUT.DerivativeLiteratureScalar.four_extraction => Physics.DerivativeLiteratureScalar.four_extraction,
  GUT.DerivativeLiteratureScalar.four_invariant => Physics.DerivativeLiteratureScalar.four_invariant,
  GUT.DerivativeLiteratureScalar.freeInput => Physics.DerivativeLiteratureScalar.freeInput,
  GUT.DerivativeLiteratureScalar.helper_direct_inverse => Physics.DerivativeLiteratureScalar.helper_direct_inverse,
  GUT.DerivativeLiteratureScalar.helper_first_onShell => Physics.DerivativeLiteratureScalar.helper_first_onShell,
  GUT.DerivativeLiteratureScalar.kinetic_as_derivatives => Physics.DerivativeLiteratureScalar.kinetic_as_derivatives,
  GUT.DerivativeLiteratureScalar.quarticDensity => Physics.DerivativeLiteratureScalar.quarticDensity,
  GUT.DerivativeLiteratureScalar.quarticDensity.eq_1 => Physics.DerivativeLiteratureScalar.quarticDensity.eq_1,
  GUT.DerivativeLiteratureScalar.quarticInput => Physics.DerivativeLiteratureScalar.quarticInput,
  GUT.DerivativeLiteratureScalar.quarticPotential => Physics.DerivativeLiteratureScalar.quarticPotential,
  GUT.DerivativeLiteratureScalar.quarticPotential.eq_1 => Physics.DerivativeLiteratureScalar.quarticPotential.eq_1,
  GUT.DerivativeLiteratureScalar.quartic_euler => Physics.DerivativeLiteratureScalar.quartic_euler,
  GUT.DerivativeLiteratureScalar.quartic_eval => Physics.DerivativeLiteratureScalar.quartic_eval,
  GUT.DerivativeLiteratureScalar.quartic_ideal => Physics.DerivativeLiteratureScalar.quartic_ideal,
  GUT.DerivativeLiteratureScalar.quartic_potential_euler => Physics.DerivativeLiteratureScalar.quartic_potential_euler,
  GUT.DerivativeLiteratureScalar.quartic_relations => Physics.DerivativeLiteratureScalar.quartic_relations,
  GUT.DerivativeLiteratureScalar.quartic_seeds => Physics.DerivativeLiteratureScalar.quartic_seeds,
  GUT.DerivativeLiteratureScalar.rawProbe => Physics.DerivativeLiteratureScalar.rawProbe,
  GUT.DerivativeLiteratureScalar.rawProbe.eq_1 => Physics.DerivativeLiteratureScalar.rawProbe.eq_1,
  GUT.DerivativeLiteratureScalar.rawProbe_field => Physics.DerivativeLiteratureScalar.rawProbe_field,
  GUT.DerivativeLiteratureScalar.rawProbe_kinetic => Physics.DerivativeLiteratureScalar.rawProbe_kinetic,
  GUT.DerivativeLiteratureScalar.second_raw_nonzero => Physics.DerivativeLiteratureScalar.second_raw_nonzero,
  GUT.DerivativeLiteratureScalar.substituted_kinetic => Physics.DerivativeLiteratureScalar.substituted_kinetic,
  GUT.DerivativeLiteratureScalar.substitution_first => Physics.DerivativeLiteratureScalar.substitution_first,
  GUT.DerivativeLiteratureScalar.substitution_first_jet => Physics.DerivativeLiteratureScalar.substitution_first_jet,
  GUT.DerivativeLiteratureScalar.substitution_second => Physics.DerivativeLiteratureScalar.substitution_second,
  GUT.DerivativeLiteratureScalar.substitution_zero => Physics.DerivativeLiteratureScalar.substitution_zero,
  GUT.DerivativeLiteratureScalar.toDirect => Physics.DerivativeLiteratureScalar.toDirect,
  GUT.DerivativeLiteratureScalar.toHelper => Physics.DerivativeLiteratureScalar.toHelper,
  GUT.DerivativeLiteratureScalar.twoDerivative => Physics.DerivativeLiteratureScalar.twoDerivative,
  GUT.DerivativeLiteratureScalar.twoDerivative.eq_1 => Physics.DerivativeLiteratureScalar.twoDerivative.eq_1,
  GUT.DerivativeLiteratureScalar.two_coefficient_zero => Physics.DerivativeLiteratureScalar.two_coefficient_zero,
  GUT.DerivativeLiteratureScalar.two_projection_zero => Physics.DerivativeLiteratureScalar.two_projection_zero,
  GUT.DerivativeLiteratureScalar.two_variation => Physics.DerivativeLiteratureScalar.two_variation,
  GUT.ScalarFirstVariation.lagrangian.eq_1 => Physics.ScalarFirstVariation.lagrangian.eq_1
]

assert_compatible GUT.DerivativeLiteratureScalar.T => Physics.DerivativeLiteratureScalar.T
assert_compatible GUT.DerivativeLiteratureScalar.direct_helper_inverse => Physics.DerivativeLiteratureScalar.direct_helper_inverse
assert_compatible GUT.DerivativeLiteratureScalar.extraction_agrees => Physics.DerivativeLiteratureScalar.extraction_agrees
assert_compatible GUT.DerivativeLiteratureScalar.fourDerivative => Physics.DerivativeLiteratureScalar.fourDerivative
assert_compatible GUT.DerivativeLiteratureScalar.fourDerivative.eq_1 => Physics.DerivativeLiteratureScalar.fourDerivative.eq_1
assert_compatible GUT.DerivativeLiteratureScalar.four_extraction => Physics.DerivativeLiteratureScalar.four_extraction
assert_compatible GUT.DerivativeLiteratureScalar.four_invariant => Physics.DerivativeLiteratureScalar.four_invariant
assert_compatible GUT.DerivativeLiteratureScalar.freeInput => Physics.DerivativeLiteratureScalar.freeInput
assert_compatible GUT.DerivativeLiteratureScalar.helper_direct_inverse => Physics.DerivativeLiteratureScalar.helper_direct_inverse
assert_compatible GUT.DerivativeLiteratureScalar.helper_first_onShell => Physics.DerivativeLiteratureScalar.helper_first_onShell
assert_compatible GUT.DerivativeLiteratureScalar.kinetic_as_derivatives => Physics.DerivativeLiteratureScalar.kinetic_as_derivatives
assert_compatible GUT.DerivativeLiteratureScalar.quarticDensity => Physics.DerivativeLiteratureScalar.quarticDensity
assert_compatible GUT.DerivativeLiteratureScalar.quarticDensity.eq_1 => Physics.DerivativeLiteratureScalar.quarticDensity.eq_1
assert_compatible GUT.DerivativeLiteratureScalar.quarticInput => Physics.DerivativeLiteratureScalar.quarticInput
assert_compatible GUT.DerivativeLiteratureScalar.quarticPotential => Physics.DerivativeLiteratureScalar.quarticPotential
assert_compatible GUT.DerivativeLiteratureScalar.quarticPotential.eq_1 => Physics.DerivativeLiteratureScalar.quarticPotential.eq_1
assert_compatible GUT.DerivativeLiteratureScalar.quartic_euler => Physics.DerivativeLiteratureScalar.quartic_euler
assert_compatible GUT.DerivativeLiteratureScalar.quartic_eval => Physics.DerivativeLiteratureScalar.quartic_eval
assert_compatible GUT.DerivativeLiteratureScalar.quartic_ideal => Physics.DerivativeLiteratureScalar.quartic_ideal
assert_compatible GUT.DerivativeLiteratureScalar.quartic_potential_euler => Physics.DerivativeLiteratureScalar.quartic_potential_euler
assert_compatible GUT.DerivativeLiteratureScalar.quartic_relations => Physics.DerivativeLiteratureScalar.quartic_relations
assert_compatible GUT.DerivativeLiteratureScalar.quartic_seeds => Physics.DerivativeLiteratureScalar.quartic_seeds
assert_compatible GUT.DerivativeLiteratureScalar.rawProbe => Physics.DerivativeLiteratureScalar.rawProbe
assert_compatible GUT.DerivativeLiteratureScalar.rawProbe.eq_1 => Physics.DerivativeLiteratureScalar.rawProbe.eq_1
assert_compatible GUT.DerivativeLiteratureScalar.rawProbe_field => Physics.DerivativeLiteratureScalar.rawProbe_field
assert_compatible GUT.DerivativeLiteratureScalar.rawProbe_kinetic => Physics.DerivativeLiteratureScalar.rawProbe_kinetic
assert_compatible GUT.DerivativeLiteratureScalar.second_raw_nonzero => Physics.DerivativeLiteratureScalar.second_raw_nonzero
assert_compatible GUT.DerivativeLiteratureScalar.substituted_kinetic => Physics.DerivativeLiteratureScalar.substituted_kinetic
assert_compatible GUT.DerivativeLiteratureScalar.substitution_first => Physics.DerivativeLiteratureScalar.substitution_first
assert_compatible GUT.DerivativeLiteratureScalar.substitution_first_jet => Physics.DerivativeLiteratureScalar.substitution_first_jet
assert_compatible GUT.DerivativeLiteratureScalar.substitution_second => Physics.DerivativeLiteratureScalar.substitution_second
assert_compatible GUT.DerivativeLiteratureScalar.substitution_zero => Physics.DerivativeLiteratureScalar.substitution_zero
assert_compatible GUT.DerivativeLiteratureScalar.toDirect => Physics.DerivativeLiteratureScalar.toDirect
assert_compatible GUT.DerivativeLiteratureScalar.toHelper => Physics.DerivativeLiteratureScalar.toHelper
assert_compatible GUT.DerivativeLiteratureScalar.twoDerivative => Physics.DerivativeLiteratureScalar.twoDerivative
assert_compatible GUT.DerivativeLiteratureScalar.twoDerivative.eq_1 => Physics.DerivativeLiteratureScalar.twoDerivative.eq_1
assert_compatible GUT.DerivativeLiteratureScalar.two_coefficient_zero => Physics.DerivativeLiteratureScalar.two_coefficient_zero
assert_compatible GUT.DerivativeLiteratureScalar.two_projection_zero => Physics.DerivativeLiteratureScalar.two_projection_zero
assert_compatible GUT.DerivativeLiteratureScalar.two_variation => Physics.DerivativeLiteratureScalar.two_variation
assert_compatible GUT.ScalarFirstVariation.lagrangian.eq_1 => Physics.ScalarFirstVariation.lagrangian.eq_1
