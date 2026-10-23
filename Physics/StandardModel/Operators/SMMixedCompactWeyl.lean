import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactWeyl
import Physics.FieldTheory.Spinor.WeylIndependentAction
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.RepresentationTheory.BiaffineStatisticalOrbits
import Math.RepresentationTheory.SL2StatisticalSpan
import Math.RepresentationTheory.StatisticalSourceRestriction
import Math.RepresentationTheory.SL2PairCompactComparison
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedCompactWeyl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedCompactWeyl.Carrier => Physics.SMMixedCompactWeyl.Carrier,
  GUT.SMMixedCompactWeyl.Pair => Physics.SMMixedCompactWeyl.Pair,
  GUT.SMMixedCompactWeyl.action => Physics.SMMixedCompactWeyl.action,
  GUT.SMMixedCompactWeyl.action_paired => Physics.SMMixedCompactWeyl.action_paired,
  GUT.SMMixedCompactWeyl.action_polynomial => Physics.SMMixedCompactWeyl.action_polynomial,
  GUT.SMMixedCompactWeyl.action_spanned => Physics.SMMixedCompactWeyl.action_spanned,
  GUT.SMMixedCompactWeyl.branch => Physics.SMMixedCompactWeyl.branch,
  GUT.SMMixedCompactWeyl.branch.eq_1 => Physics.SMMixedCompactWeyl.branch.eq_1,
  GUT.SMMixedCompactWeyl.coefficient_fixed_iff => Physics.SMMixedCompactWeyl.coefficient_fixed_iff,
  GUT.SMMixedCompactWeyl.compact => Physics.SMMixedCompactWeyl.compact,
  GUT.SMMixedCompactWeyl.direction => Physics.SMMixedCompactWeyl.direction,
  GUT.SMMixedCompactWeyl.direction.eq_1 => Physics.SMMixedCompactWeyl.direction.eq_1,
  GUT.SMMixedCompactWeyl.field => Physics.SMMixedCompactWeyl.field,
  GUT.SMMixedCompactWeyl.field.eq_1 => Physics.SMMixedCompactWeyl.field.eq_1,
  GUT.SMMixedCompactWeyl.field_affine => Physics.SMMixedCompactWeyl.field_affine,
  GUT.SMMixedCompactWeyl.field_paired => Physics.SMMixedCompactWeyl.field_paired,
  GUT.SMMixedCompactWeyl.field_spanned => Physics.SMMixedCompactWeyl.field_spanned,
  GUT.SMMixedCompactWeyl.paired => Physics.SMMixedCompactWeyl.paired,
  GUT.SMMixedCompactWeyl.source => Physics.SMMixedCompactWeyl.source,
  GUT.SMMixedCompactWeyl.source_paired => Physics.SMMixedCompactWeyl.source_paired,
  GUT.SMMixedCompactWeyl.source_polynomial => Physics.SMMixedCompactWeyl.source_polynomial,
  GUT.SMMixedCompactWeyl.source_spanned => Physics.SMMixedCompactWeyl.source_spanned,
  GUT.SMMixedCompactWeyl.spin_branch => Physics.SMMixedCompactWeyl.spin_branch,
  GUT.WeylIndependentAction.spin.eq_1 => Physics.WeylIndependentAction.spin.eq_1
]

assert_compatible GUT.SMMixedCompactWeyl.Carrier => Physics.SMMixedCompactWeyl.Carrier
assert_compatible GUT.SMMixedCompactWeyl.Pair => Physics.SMMixedCompactWeyl.Pair
assert_compatible GUT.SMMixedCompactWeyl.action => Physics.SMMixedCompactWeyl.action
assert_compatible GUT.SMMixedCompactWeyl.action_paired => Physics.SMMixedCompactWeyl.action_paired
assert_compatible GUT.SMMixedCompactWeyl.action_polynomial => Physics.SMMixedCompactWeyl.action_polynomial
assert_compatible GUT.SMMixedCompactWeyl.action_spanned => Physics.SMMixedCompactWeyl.action_spanned
assert_compatible GUT.SMMixedCompactWeyl.branch => Physics.SMMixedCompactWeyl.branch
assert_compatible GUT.SMMixedCompactWeyl.branch.eq_1 => Physics.SMMixedCompactWeyl.branch.eq_1
assert_compatible GUT.SMMixedCompactWeyl.coefficient_fixed_iff => Physics.SMMixedCompactWeyl.coefficient_fixed_iff
assert_compatible GUT.SMMixedCompactWeyl.compact => Physics.SMMixedCompactWeyl.compact
assert_compatible GUT.SMMixedCompactWeyl.direction => Physics.SMMixedCompactWeyl.direction
assert_compatible GUT.SMMixedCompactWeyl.direction.eq_1 => Physics.SMMixedCompactWeyl.direction.eq_1
assert_compatible GUT.SMMixedCompactWeyl.field => Physics.SMMixedCompactWeyl.field
assert_compatible GUT.SMMixedCompactWeyl.field.eq_1 => Physics.SMMixedCompactWeyl.field.eq_1
assert_compatible GUT.SMMixedCompactWeyl.field_affine => Physics.SMMixedCompactWeyl.field_affine
assert_compatible GUT.SMMixedCompactWeyl.field_paired => Physics.SMMixedCompactWeyl.field_paired
assert_compatible GUT.SMMixedCompactWeyl.field_spanned => Physics.SMMixedCompactWeyl.field_spanned
assert_compatible GUT.SMMixedCompactWeyl.paired => Physics.SMMixedCompactWeyl.paired
assert_compatible GUT.SMMixedCompactWeyl.source => Physics.SMMixedCompactWeyl.source
assert_compatible GUT.SMMixedCompactWeyl.source_paired => Physics.SMMixedCompactWeyl.source_paired
assert_compatible GUT.SMMixedCompactWeyl.source_polynomial => Physics.SMMixedCompactWeyl.source_polynomial
assert_compatible GUT.SMMixedCompactWeyl.source_spanned => Physics.SMMixedCompactWeyl.source_spanned
assert_compatible GUT.SMMixedCompactWeyl.spin_branch => Physics.SMMixedCompactWeyl.spin_branch
assert_compatible GUT.WeylIndependentAction.spin.eq_1 => Physics.WeylIndependentAction.spin.eq_1
