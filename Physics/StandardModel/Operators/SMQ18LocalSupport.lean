import Physics.StandardModel.Operators.Support.Quark.SMQ18LocalSupport
import Physics.StandardModel.Operators.SMQ18Support
import Physics.StandardModel.Operators.SMCombinedChargeSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQ18LocalSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQ18LocalSupport.actionEquiv => Physics.SMQ18LocalSupport.actionEquiv,
  GUT.SMQ18LocalSupport.bosonEquiv => Physics.SMQ18LocalSupport.bosonEquiv,
  GUT.SMQ18LocalSupport.boson_restrict => Physics.SMQ18LocalSupport.boson_restrict,
  GUT.SMQ18LocalSupport.charge => Physics.SMQ18LocalSupport.charge,
  GUT.SMQ18LocalSupport.compact_allowed => Physics.SMQ18LocalSupport.compact_allowed,
  GUT.SMQ18LocalSupport.flavor => Physics.SMQ18LocalSupport.flavor,
  GUT.SMQ18LocalSupport.instAddCommGroupField => Physics.SMQ18LocalSupport.instAddCommGroupField,
  GUT.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet,
  GUT.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet_1,
  GUT.SMQ18LocalSupport.kernel_allowed => Physics.SMQ18LocalSupport.kernel_allowed,
  GUT.SMQ18LocalSupport.kernel_of_compact => Physics.SMQ18LocalSupport.kernel_of_compact,
  GUT.SMQ18LocalSupport.kernel_positive => Physics.SMQ18LocalSupport.kernel_positive,
  GUT.SMQ18LocalSupport.local_allowed => Physics.SMQ18LocalSupport.local_allowed,
  GUT.SMQ18LocalSupport.pattern => Physics.SMQ18LocalSupport.pattern,
  GUT.SMQ18LocalSupport.pattern.eq_1 => Physics.SMQ18LocalSupport.pattern.eq_1,
  GUT.SMQ18LocalSupport.q18 => Physics.SMQ18LocalSupport.q18,
  GUT.SMQ18LocalSupport.rank_deficient => Physics.SMQ18LocalSupport.rank_deficient,
  GUT.SMQ18LocalSupport.restricted_allowed => Physics.SMQ18LocalSupport.restricted_allowed,
  GUT.SMQ18LocalSupport.restricted_of_coefficient => Physics.SMQ18LocalSupport.restricted_of_coefficient,
  GUT.SMQ18LocalSupport.restricted_of_presented_generation => Physics.SMQ18LocalSupport.restricted_of_presented_generation,
  GUT.SMQ18LocalSupport.sourceEquiv => Physics.SMQ18LocalSupport.sourceEquiv
]

assert_compatible GUT.SMQ18LocalSupport.actionEquiv => Physics.SMQ18LocalSupport.actionEquiv
assert_compatible GUT.SMQ18LocalSupport.bosonEquiv => Physics.SMQ18LocalSupport.bosonEquiv
assert_compatible GUT.SMQ18LocalSupport.boson_restrict => Physics.SMQ18LocalSupport.boson_restrict
assert_compatible GUT.SMQ18LocalSupport.charge => Physics.SMQ18LocalSupport.charge
assert_compatible GUT.SMQ18LocalSupport.compact_allowed => Physics.SMQ18LocalSupport.compact_allowed
assert_compatible GUT.SMQ18LocalSupport.flavor => Physics.SMQ18LocalSupport.flavor
assert_compatible GUT.SMQ18LocalSupport.instAddCommGroupField => Physics.SMQ18LocalSupport.instAddCommGroupField
assert_compatible GUT.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet
assert_compatible GUT.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMQ18LocalSupport.instAddCommGroupTensorProductComplexColorDoublet_1
assert_compatible GUT.SMQ18LocalSupport.kernel_allowed => Physics.SMQ18LocalSupport.kernel_allowed
assert_compatible GUT.SMQ18LocalSupport.kernel_of_compact => Physics.SMQ18LocalSupport.kernel_of_compact
assert_compatible GUT.SMQ18LocalSupport.kernel_positive => Physics.SMQ18LocalSupport.kernel_positive
assert_compatible GUT.SMQ18LocalSupport.local_allowed => Physics.SMQ18LocalSupport.local_allowed
assert_compatible GUT.SMQ18LocalSupport.pattern => Physics.SMQ18LocalSupport.pattern
assert_compatible GUT.SMQ18LocalSupport.pattern.eq_1 => Physics.SMQ18LocalSupport.pattern.eq_1
assert_compatible GUT.SMQ18LocalSupport.q18 => Physics.SMQ18LocalSupport.q18
assert_compatible GUT.SMQ18LocalSupport.rank_deficient => Physics.SMQ18LocalSupport.rank_deficient
assert_compatible GUT.SMQ18LocalSupport.restricted_allowed => Physics.SMQ18LocalSupport.restricted_allowed
assert_compatible GUT.SMQ18LocalSupport.restricted_of_coefficient => Physics.SMQ18LocalSupport.restricted_of_coefficient
assert_compatible GUT.SMQ18LocalSupport.restricted_of_presented_generation => Physics.SMQ18LocalSupport.restricted_of_presented_generation
assert_compatible GUT.SMQ18LocalSupport.sourceEquiv => Physics.SMQ18LocalSupport.sourceEquiv
