import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTen
import Physics.StandardModel.Operators.SMMinimumOperatorDimension
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTen instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1BelowTen.Allowed => Physics.SMB1BelowTen.Allowed,
  GUT.SMB1BelowTen.Allowed.eq_1 => Physics.SMB1BelowTen.Allowed.eq_1,
  GUT.SMB1BelowTen.Forbidden => Physics.SMB1BelowTen.Forbidden,
  GUT.SMB1BelowTen.Forbidden.eq_1 => Physics.SMB1BelowTen.Forbidden.eq_1,
  GUT.SMB1BelowTen.allowed_iff => Physics.SMB1BelowTen.allowed_iff,
  GUT.SMB1BelowTen.charge_candidates => Physics.SMB1BelowTen.charge_candidates,
  GUT.SMB1BelowTen.forbidden_iff => Physics.SMB1BelowTen.forbidden_iff,
  GUT.SMB1BelowTen.forbidden_iff_not_allowed => Physics.SMB1BelowTen.forbidden_iff_not_allowed,
  GUT.SMB1BelowTen.minus_one_sufficient => Physics.SMB1BelowTen.minus_one_sufficient,
  GUT.SMB1BelowTen.necessary => Physics.SMB1BelowTen.necessary,
  GUT.SMB1BelowTen.plus_one_sufficient => Physics.SMB1BelowTen.plus_one_sufficient,
  GUT.SMB1BelowTen.plus_three_sufficient => Physics.SMB1BelowTen.plus_three_sufficient
]

assert_compatible GUT.SMB1BelowTen.Allowed => Physics.SMB1BelowTen.Allowed
assert_compatible GUT.SMB1BelowTen.Allowed.eq_1 => Physics.SMB1BelowTen.Allowed.eq_1
assert_compatible GUT.SMB1BelowTen.Forbidden => Physics.SMB1BelowTen.Forbidden
assert_compatible GUT.SMB1BelowTen.Forbidden.eq_1 => Physics.SMB1BelowTen.Forbidden.eq_1
assert_compatible GUT.SMB1BelowTen.allowed_iff => Physics.SMB1BelowTen.allowed_iff
assert_compatible GUT.SMB1BelowTen.charge_candidates => Physics.SMB1BelowTen.charge_candidates
assert_compatible GUT.SMB1BelowTen.forbidden_iff => Physics.SMB1BelowTen.forbidden_iff
assert_compatible GUT.SMB1BelowTen.forbidden_iff_not_allowed => Physics.SMB1BelowTen.forbidden_iff_not_allowed
assert_compatible GUT.SMB1BelowTen.minus_one_sufficient => Physics.SMB1BelowTen.minus_one_sufficient
assert_compatible GUT.SMB1BelowTen.necessary => Physics.SMB1BelowTen.necessary
assert_compatible GUT.SMB1BelowTen.plus_one_sufficient => Physics.SMB1BelowTen.plus_one_sufficient
assert_compatible GUT.SMB1BelowTen.plus_three_sufficient => Physics.SMB1BelowTen.plus_three_sufficient
