import Physics.FieldTheory.Jets.Scalar.Inputs.NonDerivativeModelChecks
import Math.RepresentationTheory.NonDerivativeInputChecks
import Physics.FieldTheory.Jets.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.HiggsStandardInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.NonDerivativeModelChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NonDerivativeModelChecks.Higgs.cube => Physics.NonDerivativeModelChecks.Higgs.cube,
  GUT.NonDerivativeModelChecks.Higgs.cube_mem => Physics.NonDerivativeModelChecks.Higgs.cube_mem,
  GUT.NonDerivativeModelChecks.Higgs.extraction => Physics.NonDerivativeModelChecks.Higgs.extraction,
  GUT.NonDerivativeModelChecks.Higgs.generated_direct_values => Physics.NonDerivativeModelChecks.Higgs.generated_direct_values,
  GUT.NonDerivativeModelChecks.Higgs.imageEquiv => Physics.NonDerivativeModelChecks.Higgs.imageEquiv,
  GUT.NonDerivativeModelChecks.Higgs.image_agreement => Physics.NonDerivativeModelChecks.Higgs.image_agreement,
  GUT.NonDerivativeModelChecks.Higgs.input => Physics.NonDerivativeModelChecks.Higgs.input,
  GUT.NonDerivativeModelChecks.Higgs.potentialSource => Physics.NonDerivativeModelChecks.Higgs.potentialSource,
  GUT.NonDerivativeModelChecks.Higgs.potential_stable => Physics.NonDerivativeModelChecks.Higgs.potential_stable,
  GUT.NonDerivativeModelChecks.Higgs.power_invariant => Physics.NonDerivativeModelChecks.Higgs.power_invariant,
  GUT.NonDerivativeModelChecks.Higgs.reconstruction => Physics.NonDerivativeModelChecks.Higgs.reconstruction,
  GUT.NonDerivativeModelChecks.Higgs.restrict => Physics.NonDerivativeModelChecks.Higgs.restrict,
  GUT.NonDerivativeModelChecks.Higgs.rho_invariant => Physics.NonDerivativeModelChecks.Higgs.rho_invariant,
  GUT.NonDerivativeModelChecks.Higgs.square => Physics.NonDerivativeModelChecks.Higgs.square,
  GUT.NonDerivativeModelChecks.Higgs.square_mem => Physics.NonDerivativeModelChecks.Higgs.square_mem,
  GUT.NonDerivativeModelChecks.Scalar.freeCoefficient => Physics.NonDerivativeModelChecks.Scalar.freeCoefficient,
  GUT.NonDerivativeModelChecks.Scalar.free_extraction => Physics.NonDerivativeModelChecks.Scalar.free_extraction,
  GUT.NonDerivativeModelChecks.Scalar.free_image_dimension => Physics.NonDerivativeModelChecks.Scalar.free_image_dimension,
  GUT.NonDerivativeModelChecks.Scalar.free_value => Physics.NonDerivativeModelChecks.Scalar.free_value,
  GUT.NonDerivativeModelChecks.Scalar.interacting_one_rejected => Physics.NonDerivativeModelChecks.Scalar.interacting_one_rejected,
  GUT.NonDerivativeModelChecks.Scalar.interacting_values => Physics.NonDerivativeModelChecks.Scalar.interacting_values
]

assert_compatible GUT.NonDerivativeModelChecks.Higgs.cube => Physics.NonDerivativeModelChecks.Higgs.cube
assert_compatible GUT.NonDerivativeModelChecks.Higgs.cube_mem => Physics.NonDerivativeModelChecks.Higgs.cube_mem
assert_compatible GUT.NonDerivativeModelChecks.Higgs.extraction => Physics.NonDerivativeModelChecks.Higgs.extraction
assert_compatible GUT.NonDerivativeModelChecks.Higgs.generated_direct_values => Physics.NonDerivativeModelChecks.Higgs.generated_direct_values
assert_compatible GUT.NonDerivativeModelChecks.Higgs.imageEquiv => Physics.NonDerivativeModelChecks.Higgs.imageEquiv
assert_compatible GUT.NonDerivativeModelChecks.Higgs.image_agreement => Physics.NonDerivativeModelChecks.Higgs.image_agreement
assert_compatible GUT.NonDerivativeModelChecks.Higgs.input => Physics.NonDerivativeModelChecks.Higgs.input
assert_compatible GUT.NonDerivativeModelChecks.Higgs.potentialSource => Physics.NonDerivativeModelChecks.Higgs.potentialSource
assert_compatible GUT.NonDerivativeModelChecks.Higgs.potential_stable => Physics.NonDerivativeModelChecks.Higgs.potential_stable
assert_compatible GUT.NonDerivativeModelChecks.Higgs.power_invariant => Physics.NonDerivativeModelChecks.Higgs.power_invariant
assert_compatible GUT.NonDerivativeModelChecks.Higgs.reconstruction => Physics.NonDerivativeModelChecks.Higgs.reconstruction
assert_compatible GUT.NonDerivativeModelChecks.Higgs.restrict => Physics.NonDerivativeModelChecks.Higgs.restrict
assert_compatible GUT.NonDerivativeModelChecks.Higgs.rho_invariant => Physics.NonDerivativeModelChecks.Higgs.rho_invariant
assert_compatible GUT.NonDerivativeModelChecks.Higgs.square => Physics.NonDerivativeModelChecks.Higgs.square
assert_compatible GUT.NonDerivativeModelChecks.Higgs.square_mem => Physics.NonDerivativeModelChecks.Higgs.square_mem
assert_compatible GUT.NonDerivativeModelChecks.Scalar.freeCoefficient => Physics.NonDerivativeModelChecks.Scalar.freeCoefficient
assert_compatible GUT.NonDerivativeModelChecks.Scalar.free_extraction => Physics.NonDerivativeModelChecks.Scalar.free_extraction
assert_compatible GUT.NonDerivativeModelChecks.Scalar.free_image_dimension => Physics.NonDerivativeModelChecks.Scalar.free_image_dimension
assert_compatible GUT.NonDerivativeModelChecks.Scalar.free_value => Physics.NonDerivativeModelChecks.Scalar.free_value
assert_compatible GUT.NonDerivativeModelChecks.Scalar.interacting_one_rejected => Physics.NonDerivativeModelChecks.Scalar.interacting_one_rejected
assert_compatible GUT.NonDerivativeModelChecks.Scalar.interacting_values => Physics.NonDerivativeModelChecks.Scalar.interacting_values
