import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoScalarSelection
import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Physics.StandardModel.Operators.ResidualSelectionCriteria
import Physics.StandardModel.Operators.CyclicResidualSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoScalarSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoScalarSelection.Neutral => Physics.DeltaBTwoScalarSelection.Neutral,
  GUT.DeltaBTwoScalarSelection.allowed_iff => Physics.DeltaBTwoScalarSelection.allowed_iff,
  GUT.DeltaBTwoScalarSelection.allowed_onFields_iff => Physics.DeltaBTwoScalarSelection.allowed_onFields_iff,
  GUT.DeltaBTwoScalarSelection.coefficientEquiv => Physics.DeltaBTwoScalarSelection.coefficientEquiv,
  GUT.DeltaBTwoScalarSelection.finrank_neutral => Physics.DeltaBTwoScalarSelection.finrank_neutral,
  GUT.DeltaBTwoScalarSelection.forbidden_iff => Physics.DeltaBTwoScalarSelection.forbidden_iff,
  GUT.DeltaBTwoScalarSelection.forbidden_onFields_iff => Physics.DeltaBTwoScalarSelection.forbidden_onFields_iff,
  GUT.DeltaBTwoScalarSelection.inverse_twoProbes => Physics.DeltaBTwoScalarSelection.inverse_twoProbes,
  GUT.DeltaBTwoScalarSelection.neutral_invariant => Physics.DeltaBTwoScalarSelection.neutral_invariant,
  GUT.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv => Physics.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv,
  GUT.DeltaBTwoScalarSelection.pairEquiv => Physics.DeltaBTwoScalarSelection.pairEquiv,
  GUT.DeltaBTwoScalarSelection.reconstruct_twoProbes => Physics.DeltaBTwoScalarSelection.reconstruct_twoProbes,
  GUT.DeltaBTwoScalarSelection.residual_action => Physics.DeltaBTwoScalarSelection.residual_action,
  GUT.DeltaBTwoScalarSelection.scalar_map => Physics.DeltaBTwoScalarSelection.scalar_map,
  GUT.DeltaBTwoScalarSelection.slot_action => Physics.DeltaBTwoScalarSelection.slot_action,
  GUT.DeltaBTwoScalarSelection.total => Physics.DeltaBTwoScalarSelection.total,
  GUT.DeltaBTwoScalarSelection.total.eq_1 => Physics.DeltaBTwoScalarSelection.total.eq_1,
  GUT.DeltaBTwoScalarSelection.twoProbeEquiv => Physics.DeltaBTwoScalarSelection.twoProbeEquiv
]

assert_compatible GUT.DeltaBTwoScalarSelection.Neutral => Physics.DeltaBTwoScalarSelection.Neutral
assert_compatible GUT.DeltaBTwoScalarSelection.allowed_iff => Physics.DeltaBTwoScalarSelection.allowed_iff
assert_compatible GUT.DeltaBTwoScalarSelection.allowed_onFields_iff => Physics.DeltaBTwoScalarSelection.allowed_onFields_iff
assert_compatible GUT.DeltaBTwoScalarSelection.coefficientEquiv => Physics.DeltaBTwoScalarSelection.coefficientEquiv
assert_compatible GUT.DeltaBTwoScalarSelection.finrank_neutral => Physics.DeltaBTwoScalarSelection.finrank_neutral
assert_compatible GUT.DeltaBTwoScalarSelection.forbidden_iff => Physics.DeltaBTwoScalarSelection.forbidden_iff
assert_compatible GUT.DeltaBTwoScalarSelection.forbidden_onFields_iff => Physics.DeltaBTwoScalarSelection.forbidden_onFields_iff
assert_compatible GUT.DeltaBTwoScalarSelection.inverse_twoProbes => Physics.DeltaBTwoScalarSelection.inverse_twoProbes
assert_compatible GUT.DeltaBTwoScalarSelection.neutral_invariant => Physics.DeltaBTwoScalarSelection.neutral_invariant
assert_compatible GUT.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv => Physics.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv
assert_compatible GUT.DeltaBTwoScalarSelection.pairEquiv => Physics.DeltaBTwoScalarSelection.pairEquiv
assert_compatible GUT.DeltaBTwoScalarSelection.reconstruct_twoProbes => Physics.DeltaBTwoScalarSelection.reconstruct_twoProbes
assert_compatible GUT.DeltaBTwoScalarSelection.residual_action => Physics.DeltaBTwoScalarSelection.residual_action
assert_compatible GUT.DeltaBTwoScalarSelection.scalar_map => Physics.DeltaBTwoScalarSelection.scalar_map
assert_compatible GUT.DeltaBTwoScalarSelection.slot_action => Physics.DeltaBTwoScalarSelection.slot_action
assert_compatible GUT.DeltaBTwoScalarSelection.total => Physics.DeltaBTwoScalarSelection.total
assert_compatible GUT.DeltaBTwoScalarSelection.total.eq_1 => Physics.DeltaBTwoScalarSelection.total.eq_1
assert_compatible GUT.DeltaBTwoScalarSelection.twoProbeEquiv => Physics.DeltaBTwoScalarSelection.twoProbeEquiv
