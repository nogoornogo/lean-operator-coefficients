import Physics.StandardModel.Operators.Support.Dimension.SMLKernelDimension
import Physics.StandardModel.Operators.SMLContinuousCharacter
import Physics.StandardModel.Operators.SMConstantContentRanks
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMLKernelDimension instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMConstantContentRanks.dimension.eq_1 => Physics.SMConstantContentRanks.dimension.eq_1,
  GUT.SMLKernelDimension.action_color_fixed => Physics.SMLKernelDimension.action_color_fixed,
  GUT.SMLKernelDimension.action_hyper_fixed => Physics.SMLKernelDimension.action_hyper_fixed,
  GUT.SMLKernelDimension.allowed_iff => Physics.SMLKernelDimension.allowed_iff,
  GUT.SMLKernelDimension.allowed_neutral_iff => Physics.SMLKernelDimension.allowed_neutral_iff,
  GUT.SMLKernelDimension.boson_color_fixed => Physics.SMLKernelDimension.boson_color_fixed,
  GUT.SMLKernelDimension.coefficientEquiv => Physics.SMLKernelDimension.coefficientEquiv,
  GUT.SMLKernelDimension.full_fixed_of_pair => Physics.SMLKernelDimension.full_fixed_of_pair,
  GUT.SMLKernelDimension.kernel_dimension => Physics.SMLKernelDimension.kernel_dimension,
  GUT.SMLKernelDimension.multiplicity => Physics.SMLKernelDimension.multiplicity,
  GUT.SMLKernelDimension.multiplicity_above_capacity => Physics.SMLKernelDimension.multiplicity_above_capacity,
  GUT.SMLKernelDimension.multiplicity_llhh => Physics.SMLKernelDimension.multiplicity_llhh,
  GUT.SMLKernelDimension.multiplicity_odd => Physics.SMLKernelDimension.multiplicity_odd,
  GUT.SMLKernelDimension.pattern => Physics.SMLKernelDimension.pattern,
  GUT.SMLKernelDimension.rank_add_multiplicity => Physics.SMLKernelDimension.rank_add_multiplicity,
  GUT.SMLKernelDimension.source_color_fixed => Physics.SMLKernelDimension.source_color_fixed
]

assert_compatible GUT.SMConstantContentRanks.dimension.eq_1 => Physics.SMConstantContentRanks.dimension.eq_1
assert_compatible GUT.SMLKernelDimension.action_color_fixed => Physics.SMLKernelDimension.action_color_fixed
assert_compatible GUT.SMLKernelDimension.action_hyper_fixed => Physics.SMLKernelDimension.action_hyper_fixed
assert_compatible GUT.SMLKernelDimension.allowed_iff => Physics.SMLKernelDimension.allowed_iff
assert_compatible GUT.SMLKernelDimension.allowed_neutral_iff => Physics.SMLKernelDimension.allowed_neutral_iff
assert_compatible GUT.SMLKernelDimension.boson_color_fixed => Physics.SMLKernelDimension.boson_color_fixed
assert_compatible GUT.SMLKernelDimension.coefficientEquiv => Physics.SMLKernelDimension.coefficientEquiv
assert_compatible GUT.SMLKernelDimension.full_fixed_of_pair => Physics.SMLKernelDimension.full_fixed_of_pair
assert_compatible GUT.SMLKernelDimension.kernel_dimension => Physics.SMLKernelDimension.kernel_dimension
assert_compatible GUT.SMLKernelDimension.multiplicity => Physics.SMLKernelDimension.multiplicity
assert_compatible GUT.SMLKernelDimension.multiplicity_above_capacity => Physics.SMLKernelDimension.multiplicity_above_capacity
assert_compatible GUT.SMLKernelDimension.multiplicity_llhh => Physics.SMLKernelDimension.multiplicity_llhh
assert_compatible GUT.SMLKernelDimension.multiplicity_odd => Physics.SMLKernelDimension.multiplicity_odd
assert_compatible GUT.SMLKernelDimension.pattern => Physics.SMLKernelDimension.pattern
assert_compatible GUT.SMLKernelDimension.rank_add_multiplicity => Physics.SMLKernelDimension.rank_add_multiplicity
assert_compatible GUT.SMLKernelDimension.source_color_fixed => Physics.SMLKernelDimension.source_color_fixed
