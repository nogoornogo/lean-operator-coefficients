import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedInput
import Physics.StandardModel.Operators.DeltaLOneSignedFields
import Math.RepresentationTheory.MixedWeightSupport
import Physics.FieldTheory.Spinor.WeylCentralParity
import Math.RepresentationTheory.MixedSpeciesExt
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvMixedInput.Coefficient => Physics.BnvMixedInput.Coefficient,
  GUT.BnvMixedInput.ScalarField => Physics.BnvMixedInput.ScalarField,
  GUT.BnvMixedInput.ScalarGaugeCarrier => Physics.BnvMixedInput.ScalarGaugeCarrier,
  GUT.BnvMixedInput.ScalarSpecies => Physics.BnvMixedInput.ScalarSpecies,
  GUT.BnvMixedInput.baryon_sum_bounds => Physics.BnvMixedInput.baryon_sum_bounds,
  GUT.BnvMixedInput.bnvSector => Physics.BnvMixedInput.bnvSector,
  GUT.BnvMixedInput.bnv_degrees_le_seven => Physics.BnvMixedInput.bnv_degrees_le_seven,
  GUT.BnvMixedInput.bnv_eq_zero_below_six => Physics.BnvMixedInput.bnv_eq_zero_below_six,
  GUT.BnvMixedInput.bnv_eq_zero_outside_seven_degrees => Physics.BnvMixedInput.bnv_eq_zero_outside_seven_degrees,
  GUT.BnvMixedInput.bnv_fermion_classes_le_eleven => Physics.BnvMixedInput.bnv_fermion_classes_le_eleven,
  GUT.BnvMixedInput.bnv_minimum_dimension => Physics.BnvMixedInput.bnv_minimum_dimension,
  GUT.BnvMixedInput.bounded => Physics.BnvMixedInput.bounded,
  GUT.BnvMixedInput.bounded_eq_zero_below_six => Physics.BnvMixedInput.bounded_eq_zero_below_six,
  GUT.BnvMixedInput.degree_window => Physics.BnvMixedInput.degree_window,
  GUT.BnvMixedInput.even_fermions_of_nonzero => Physics.BnvMixedInput.even_fermions_of_nonzero,
  GUT.BnvMixedInput.field_minus => Physics.BnvMixedInput.field_minus,
  GUT.BnvMixedInput.fullMinus => Physics.BnvMixedInput.fullMinus,
  GUT.BnvMixedInput.fullMinus.eq_1 => Physics.BnvMixedInput.fullMinus.eq_1,
  GUT.BnvMixedInput.hypercharge_of_nonzero => Physics.BnvMixedInput.hypercharge_of_nonzero,
  GUT.BnvMixedInput.instAddCommGroupScalarGaugeCarrier => Physics.BnvMixedInput.instAddCommGroupScalarGaugeCarrier,
  GUT.BnvMixedInput.instModuleComplexScalarGaugeCarrier => Physics.BnvMixedInput.instModuleComplexScalarGaugeCarrier,
  GUT.BnvMixedInput.scalarField => Physics.BnvMixedInput.scalarField,
  GUT.BnvMixedInput.scalarField.eq_1 => Physics.BnvMixedInput.scalarField.eq_1,
  GUT.BnvMixedInput.scalarField_center => Physics.BnvMixedInput.scalarField_center,
  GUT.BnvMixedInput.scalarField_hypercharge => Physics.BnvMixedInput.scalarField_hypercharge,
  GUT.BnvMixedInput.scalarField_minus => Physics.BnvMixedInput.scalarField_minus,
  GUT.BnvMixedInput.scalarGauge => Physics.BnvMixedInput.scalarGauge,
  GUT.BnvMixedInput.scalarGauge_center => Physics.BnvMixedInput.scalarGauge_center,
  GUT.BnvMixedInput.scalarGauge_hypercharge => Physics.BnvMixedInput.scalarGauge_hypercharge,
  GUT.BnvMixedInput.scalarHypercharge => Physics.BnvMixedInput.scalarHypercharge,
  GUT.BnvMixedInput.scalarRepresentation => Physics.BnvMixedInput.scalarRepresentation,
  GUT.BnvMixedInput.triality_of_nonzero => Physics.BnvMixedInput.triality_of_nonzero,
  GUT.BnvMixedInput.value => Physics.BnvMixedInput.value,
  GUT.BnvMixedInput.value_ext => Physics.BnvMixedInput.value_ext
]

assert_compatible GUT.BnvMixedInput.Coefficient => Physics.BnvMixedInput.Coefficient
assert_compatible GUT.BnvMixedInput.ScalarField => Physics.BnvMixedInput.ScalarField
assert_compatible GUT.BnvMixedInput.ScalarGaugeCarrier => Physics.BnvMixedInput.ScalarGaugeCarrier
assert_compatible GUT.BnvMixedInput.ScalarSpecies => Physics.BnvMixedInput.ScalarSpecies
assert_compatible GUT.BnvMixedInput.baryon_sum_bounds => Physics.BnvMixedInput.baryon_sum_bounds
assert_compatible GUT.BnvMixedInput.bnvSector => Physics.BnvMixedInput.bnvSector
assert_compatible GUT.BnvMixedInput.bnv_degrees_le_seven => Physics.BnvMixedInput.bnv_degrees_le_seven
assert_compatible GUT.BnvMixedInput.bnv_eq_zero_below_six => Physics.BnvMixedInput.bnv_eq_zero_below_six
assert_compatible GUT.BnvMixedInput.bnv_eq_zero_outside_seven_degrees => Physics.BnvMixedInput.bnv_eq_zero_outside_seven_degrees
assert_compatible GUT.BnvMixedInput.bnv_fermion_classes_le_eleven => Physics.BnvMixedInput.bnv_fermion_classes_le_eleven
assert_compatible GUT.BnvMixedInput.bnv_minimum_dimension => Physics.BnvMixedInput.bnv_minimum_dimension
assert_compatible GUT.BnvMixedInput.bounded => Physics.BnvMixedInput.bounded
assert_compatible GUT.BnvMixedInput.bounded_eq_zero_below_six => Physics.BnvMixedInput.bounded_eq_zero_below_six
assert_compatible GUT.BnvMixedInput.degree_window => Physics.BnvMixedInput.degree_window
assert_compatible GUT.BnvMixedInput.even_fermions_of_nonzero => Physics.BnvMixedInput.even_fermions_of_nonzero
assert_compatible GUT.BnvMixedInput.field_minus => Physics.BnvMixedInput.field_minus
assert_compatible GUT.BnvMixedInput.fullMinus => Physics.BnvMixedInput.fullMinus
assert_compatible GUT.BnvMixedInput.fullMinus.eq_1 => Physics.BnvMixedInput.fullMinus.eq_1
assert_compatible GUT.BnvMixedInput.hypercharge_of_nonzero => Physics.BnvMixedInput.hypercharge_of_nonzero
assert_compatible GUT.BnvMixedInput.instAddCommGroupScalarGaugeCarrier => Physics.BnvMixedInput.instAddCommGroupScalarGaugeCarrier
assert_compatible GUT.BnvMixedInput.instModuleComplexScalarGaugeCarrier => Physics.BnvMixedInput.instModuleComplexScalarGaugeCarrier
assert_compatible GUT.BnvMixedInput.scalarField => Physics.BnvMixedInput.scalarField
assert_compatible GUT.BnvMixedInput.scalarField.eq_1 => Physics.BnvMixedInput.scalarField.eq_1
assert_compatible GUT.BnvMixedInput.scalarField_center => Physics.BnvMixedInput.scalarField_center
assert_compatible GUT.BnvMixedInput.scalarField_hypercharge => Physics.BnvMixedInput.scalarField_hypercharge
assert_compatible GUT.BnvMixedInput.scalarField_minus => Physics.BnvMixedInput.scalarField_minus
assert_compatible GUT.BnvMixedInput.scalarGauge => Physics.BnvMixedInput.scalarGauge
assert_compatible GUT.BnvMixedInput.scalarGauge_center => Physics.BnvMixedInput.scalarGauge_center
assert_compatible GUT.BnvMixedInput.scalarGauge_hypercharge => Physics.BnvMixedInput.scalarGauge_hypercharge
assert_compatible GUT.BnvMixedInput.scalarHypercharge => Physics.BnvMixedInput.scalarHypercharge
assert_compatible GUT.BnvMixedInput.scalarRepresentation => Physics.BnvMixedInput.scalarRepresentation
assert_compatible GUT.BnvMixedInput.triality_of_nonzero => Physics.BnvMixedInput.triality_of_nonzero
assert_compatible GUT.BnvMixedInput.value => Physics.BnvMixedInput.value
assert_compatible GUT.BnvMixedInput.value_ext => Physics.BnvMixedInput.value_ext
