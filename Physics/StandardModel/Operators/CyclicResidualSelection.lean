import Physics.StandardModel.Operators.Selection.CyclicResidualSelection
import Math.RepresentationTheory.CyclicCharge
import Physics.StandardModel.Operators.ScalarResidualSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.CyclicResidualSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CyclicResidualSelection.Charges => Physics.CyclicResidualSelection.Charges,
  GUT.CyclicResidualSelection.allowed_family_iff => Physics.CyclicResidualSelection.allowed_family_iff,
  GUT.CyclicResidualSelection.allowed_total_iff => Physics.CyclicResidualSelection.allowed_total_iff,
  GUT.CyclicResidualSelection.allowed_weinberg_iff => Physics.CyclicResidualSelection.allowed_weinberg_iff,
  GUT.CyclicResidualSelection.familyCharge => Physics.CyclicResidualSelection.familyCharge,
  GUT.CyclicResidualSelection.familyCharge.eq_1 => Physics.CyclicResidualSelection.familyCharge.eq_1,
  GUT.CyclicResidualSelection.flavor => Physics.CyclicResidualSelection.flavor,
  GUT.CyclicResidualSelection.forbidden_family_iff => Physics.CyclicResidualSelection.forbidden_family_iff,
  GUT.CyclicResidualSelection.forbidden_total_iff => Physics.CyclicResidualSelection.forbidden_total_iff,
  GUT.CyclicResidualSelection.neutral_four_iff => Physics.CyclicResidualSelection.neutral_four_iff,
  GUT.CyclicResidualSelection.order_one_rejected => Physics.CyclicResidualSelection.order_one_rejected,
  GUT.CyclicResidualSelection.quarkParity => Physics.CyclicResidualSelection.quarkParity,
  GUT.CyclicResidualSelection.quarkParity_conditions => Physics.CyclicResidualSelection.quarkParity_conditions,
  GUT.CyclicResidualSelection.quarkParity_selection => Physics.CyclicResidualSelection.quarkParity_selection,
  GUT.CyclicResidualSelection.signedCharges => Physics.CyclicResidualSelection.signedCharges,
  GUT.CyclicResidualSelection.simultaneous_iff => Physics.CyclicResidualSelection.simultaneous_iff,
  GUT.CyclicResidualSelection.trivial_assignment_rejected => Physics.CyclicResidualSelection.trivial_assignment_rejected
]

assert_compatible GUT.CyclicResidualSelection.Charges => Physics.CyclicResidualSelection.Charges
assert_compatible GUT.CyclicResidualSelection.allowed_family_iff => Physics.CyclicResidualSelection.allowed_family_iff
assert_compatible GUT.CyclicResidualSelection.allowed_total_iff => Physics.CyclicResidualSelection.allowed_total_iff
assert_compatible GUT.CyclicResidualSelection.allowed_weinberg_iff => Physics.CyclicResidualSelection.allowed_weinberg_iff
assert_compatible GUT.CyclicResidualSelection.familyCharge => Physics.CyclicResidualSelection.familyCharge
assert_compatible GUT.CyclicResidualSelection.familyCharge.eq_1 => Physics.CyclicResidualSelection.familyCharge.eq_1
assert_compatible GUT.CyclicResidualSelection.flavor => Physics.CyclicResidualSelection.flavor
assert_compatible GUT.CyclicResidualSelection.forbidden_family_iff => Physics.CyclicResidualSelection.forbidden_family_iff
assert_compatible GUT.CyclicResidualSelection.forbidden_total_iff => Physics.CyclicResidualSelection.forbidden_total_iff
assert_compatible GUT.CyclicResidualSelection.neutral_four_iff => Physics.CyclicResidualSelection.neutral_four_iff
assert_compatible GUT.CyclicResidualSelection.order_one_rejected => Physics.CyclicResidualSelection.order_one_rejected
assert_compatible GUT.CyclicResidualSelection.quarkParity => Physics.CyclicResidualSelection.quarkParity
assert_compatible GUT.CyclicResidualSelection.quarkParity_conditions => Physics.CyclicResidualSelection.quarkParity_conditions
assert_compatible GUT.CyclicResidualSelection.quarkParity_selection => Physics.CyclicResidualSelection.quarkParity_selection
assert_compatible GUT.CyclicResidualSelection.signedCharges => Physics.CyclicResidualSelection.signedCharges
assert_compatible GUT.CyclicResidualSelection.simultaneous_iff => Physics.CyclicResidualSelection.simultaneous_iff
assert_compatible GUT.CyclicResidualSelection.trivial_assignment_rejected => Physics.CyclicResidualSelection.trivial_assignment_rejected
