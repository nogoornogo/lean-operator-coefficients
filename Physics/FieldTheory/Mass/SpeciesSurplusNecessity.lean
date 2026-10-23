import Physics.FieldTheory.Mass.Surplus.SpeciesSurplusNecessity
import Physics.FieldTheory.Mass.PhysicalSpeciesCopySurplus
import Math.RepresentationTheory.ProtectionConstraintPullback
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.SpeciesSurplusNecessity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SpeciesSurplusNecessity.ForbiddenExterior => Physics.SpeciesSurplusNecessity.ForbiddenExterior,
  GUT.SpeciesSurplusNecessity.bottleneck => Physics.SpeciesSurplusNecessity.bottleneck,
  GUT.SpeciesSurplusNecessity.count_bottleneck => Physics.SpeciesSurplusNecessity.count_bottleneck,
  GUT.SpeciesSurplusNecessity.count_parameter_retain => Physics.SpeciesSurplusNecessity.count_parameter_retain,
  GUT.SpeciesSurplusNecessity.no_joint_surplus => Physics.SpeciesSurplusNecessity.no_joint_surplus
]

assert_compatible GUT.SpeciesSurplusNecessity.ForbiddenExterior => Physics.SpeciesSurplusNecessity.ForbiddenExterior
assert_compatible GUT.SpeciesSurplusNecessity.bottleneck => Physics.SpeciesSurplusNecessity.bottleneck
assert_compatible GUT.SpeciesSurplusNecessity.count_bottleneck => Physics.SpeciesSurplusNecessity.count_bottleneck
assert_compatible GUT.SpeciesSurplusNecessity.count_parameter_retain => Physics.SpeciesSurplusNecessity.count_parameter_retain
assert_compatible GUT.SpeciesSurplusNecessity.no_joint_surplus => Physics.SpeciesSurplusNecessity.no_joint_surplus
