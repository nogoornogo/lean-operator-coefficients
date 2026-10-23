import Physics.StandardModel.Operators.Support.Dimension.SMChargeDegreeBounds
import Physics.StandardModel.Operators.SMQLPatternRequests
import Physics.StandardModel.Operators.InverseLeptonParitySelection
import Physics.StandardModel.Operators.SMJointHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMChargeDegreeBounds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMChargeDegreeBounds.b1_dimension_nine => Physics.SMChargeDegreeBounds.b1_dimension_nine,
  GUT.SMChargeDegreeBounds.b1_six_fermions => Physics.SMChargeDegreeBounds.b1_six_fermions,
  GUT.SMChargeDegreeBounds.charge_degree => Physics.SMChargeDegreeBounds.charge_degree,
  GUT.SMChargeDegreeBounds.dimension_lower => Physics.SMChargeDegreeBounds.dimension_lower,
  GUT.SMChargeDegreeBounds.original_degree_lower => Physics.SMChargeDegreeBounds.original_degree_lower,
  GUT.SMChargeDegreeBounds.original_even => Physics.SMChargeDegreeBounds.original_even,
  GUT.SMChargeDegreeBounds.original_lepton_lower => Physics.SMChargeDegreeBounds.original_lepton_lower,
  GUT.SMChargeDegreeBounds.original_parity => Physics.SMChargeDegreeBounds.original_parity,
  GUT.SMChargeDegreeBounds.residual_linear => Physics.SMChargeDegreeBounds.residual_linear,
  GUT.SMChargeDegreeBounds.selected_degree => Physics.SMChargeDegreeBounds.selected_degree,
  GUT.SMChargeDegreeBounds.signed_charge_linear => Physics.SMChargeDegreeBounds.signed_charge_linear,
  GUT.SMChargeDegreeBounds.species_abs => Physics.SMChargeDegreeBounds.species_abs,
  GUT.SMChargeDegreeBounds.twiceDimension => Physics.SMChargeDegreeBounds.twiceDimension,
  GUT.SMQLPatternRequests.blCharge.eq_1 => Physics.SMQLPatternRequests.blCharge.eq_1
]

assert_compatible GUT.SMChargeDegreeBounds.b1_dimension_nine => Physics.SMChargeDegreeBounds.b1_dimension_nine
assert_compatible GUT.SMChargeDegreeBounds.b1_six_fermions => Physics.SMChargeDegreeBounds.b1_six_fermions
assert_compatible GUT.SMChargeDegreeBounds.charge_degree => Physics.SMChargeDegreeBounds.charge_degree
assert_compatible GUT.SMChargeDegreeBounds.dimension_lower => Physics.SMChargeDegreeBounds.dimension_lower
assert_compatible GUT.SMChargeDegreeBounds.original_degree_lower => Physics.SMChargeDegreeBounds.original_degree_lower
assert_compatible GUT.SMChargeDegreeBounds.original_even => Physics.SMChargeDegreeBounds.original_even
assert_compatible GUT.SMChargeDegreeBounds.original_lepton_lower => Physics.SMChargeDegreeBounds.original_lepton_lower
assert_compatible GUT.SMChargeDegreeBounds.original_parity => Physics.SMChargeDegreeBounds.original_parity
assert_compatible GUT.SMChargeDegreeBounds.residual_linear => Physics.SMChargeDegreeBounds.residual_linear
assert_compatible GUT.SMChargeDegreeBounds.selected_degree => Physics.SMChargeDegreeBounds.selected_degree
assert_compatible GUT.SMChargeDegreeBounds.signed_charge_linear => Physics.SMChargeDegreeBounds.signed_charge_linear
assert_compatible GUT.SMChargeDegreeBounds.species_abs => Physics.SMChargeDegreeBounds.species_abs
assert_compatible GUT.SMChargeDegreeBounds.twiceDimension => Physics.SMChargeDegreeBounds.twiceDimension
assert_compatible GUT.SMQLPatternRequests.blCharge.eq_1 => Physics.SMQLPatternRequests.blCharge.eq_1
