import Physics.FieldTheory.Mass.Surplus.BalancedSpeciesSurplusControl
import Physics.FieldTheory.Mass.SpeciesSurplusNecessity
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.BalancedSpeciesSurplusControl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BalancedSpeciesSurplusControl.Field => Physics.BalancedSpeciesSurplusControl.Field,
  GUT.BalancedSpeciesSurplusControl.converse_counterexample => Physics.BalancedSpeciesSurplusControl.converse_counterexample,
  GUT.BalancedSpeciesSurplusControl.eAction => Physics.BalancedSpeciesSurplusControl.eAction,
  GUT.BalancedSpeciesSurplusControl.fields => Physics.BalancedSpeciesSurplusControl.fields,
  GUT.BalancedSpeciesSurplusControl.instAddCommGroupField => Physics.BalancedSpeciesSurplusControl.instAddCommGroupField,
  GUT.BalancedSpeciesSurplusControl.mass => Physics.BalancedSpeciesSurplusControl.mass,
  GUT.BalancedSpeciesSurplusControl.no_surplus => Physics.BalancedSpeciesSurplusControl.no_surplus,
  GUT.BalancedSpeciesSurplusControl.not_forbidden => Physics.BalancedSpeciesSurplusControl.not_forbidden,
  GUT.BalancedSpeciesSurplusControl.physical_light_coefficient => Physics.BalancedSpeciesSurplusControl.physical_light_coefficient,
  GUT.BalancedSpeciesSurplusControl.qAction => Physics.BalancedSpeciesSurplusControl.qAction,
  GUT.BalancedSpeciesSurplusControl.realization => Physics.BalancedSpeciesSurplusControl.realization,
  GUT.BalancedSpeciesSurplusControl.uAction => Physics.BalancedSpeciesSurplusControl.uAction,
  GUT.BalancedSpeciesSurplusControl.zeroKernelSplit => Physics.BalancedSpeciesSurplusControl.zeroKernelSplit,
  GUT.BalancedSpeciesSurplusControl.zeroSpecies => Physics.BalancedSpeciesSurplusControl.zeroSpecies
]

assert_compatible GUT.BalancedSpeciesSurplusControl.Field => Physics.BalancedSpeciesSurplusControl.Field
assert_compatible GUT.BalancedSpeciesSurplusControl.converse_counterexample => Physics.BalancedSpeciesSurplusControl.converse_counterexample
assert_compatible GUT.BalancedSpeciesSurplusControl.eAction => Physics.BalancedSpeciesSurplusControl.eAction
assert_compatible GUT.BalancedSpeciesSurplusControl.fields => Physics.BalancedSpeciesSurplusControl.fields
assert_compatible GUT.BalancedSpeciesSurplusControl.instAddCommGroupField => Physics.BalancedSpeciesSurplusControl.instAddCommGroupField
assert_compatible GUT.BalancedSpeciesSurplusControl.mass => Physics.BalancedSpeciesSurplusControl.mass
assert_compatible GUT.BalancedSpeciesSurplusControl.no_surplus => Physics.BalancedSpeciesSurplusControl.no_surplus
assert_compatible GUT.BalancedSpeciesSurplusControl.not_forbidden => Physics.BalancedSpeciesSurplusControl.not_forbidden
assert_compatible GUT.BalancedSpeciesSurplusControl.physical_light_coefficient => Physics.BalancedSpeciesSurplusControl.physical_light_coefficient
assert_compatible GUT.BalancedSpeciesSurplusControl.qAction => Physics.BalancedSpeciesSurplusControl.qAction
assert_compatible GUT.BalancedSpeciesSurplusControl.realization => Physics.BalancedSpeciesSurplusControl.realization
assert_compatible GUT.BalancedSpeciesSurplusControl.uAction => Physics.BalancedSpeciesSurplusControl.uAction
assert_compatible GUT.BalancedSpeciesSurplusControl.zeroKernelSplit => Physics.BalancedSpeciesSurplusControl.zeroKernelSplit
assert_compatible GUT.BalancedSpeciesSurplusControl.zeroSpecies => Physics.BalancedSpeciesSurplusControl.zeroSpecies
