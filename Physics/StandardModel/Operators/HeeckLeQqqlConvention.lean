import Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlConvention
import Physics.StandardModel.Operators.QqqlFlavorComponents
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeQqqlConvention.literal => Physics.HeeckLeQqqlConvention.literal,
  GUT.HeeckLeQqqlConvention.orbit => Physics.HeeckLeQqqlConvention.orbit,
  GUT.HeeckLeQqqlConvention.orbit.eq_1 => Physics.HeeckLeQqqlConvention.orbit.eq_1,
  GUT.HeeckLeQqqlConvention.orbit_inverse => Physics.HeeckLeQqqlConvention.orbit_inverse,
  GUT.HeeckLeQqqlConvention.paperLocal => Physics.HeeckLeQqqlConvention.paperLocal,
  GUT.HeeckLeQqqlConvention.paperLocal.eq_1 => Physics.HeeckLeQqqlConvention.paperLocal.eq_1,
  GUT.HeeckLeQqqlConvention.seed => Physics.HeeckLeQqqlConvention.seed,
  GUT.HeeckLeQqqlConvention.seed.eq_1 => Physics.HeeckLeQqqlConvention.seed.eq_1,
  GUT.HeeckLeQqqlConvention.seed_alternating_nonzero => Physics.HeeckLeQqqlConvention.seed_alternating_nonzero,
  GUT.HeeckLeQqqlConvention.seed_components => Physics.HeeckLeQqqlConvention.seed_components,
  GUT.HeeckLeQqqlConvention.seed_mixed_nonzero => Physics.HeeckLeQqqlConvention.seed_mixed_nonzero,
  GUT.HeeckLeQqqlConvention.seed_symmetric_nonzero => Physics.HeeckLeQqqlConvention.seed_symmetric_nonzero,
  GUT.HeeckLeQqqlConvention.source => Physics.HeeckLeQqqlConvention.source,
  GUT.HeeckLeQqqlConvention.source.eq_1 => Physics.HeeckLeQqqlConvention.source.eq_1,
  GUT.HeeckLeQqqlConvention.source_apply => Physics.HeeckLeQqqlConvention.source_apply,
  GUT.HeeckLeQqqlConvention.source_orbit => Physics.HeeckLeQqqlConvention.source_orbit
]

assert_compatible GUT.HeeckLeQqqlConvention.literal => Physics.HeeckLeQqqlConvention.literal
assert_compatible GUT.HeeckLeQqqlConvention.orbit => Physics.HeeckLeQqqlConvention.orbit
assert_compatible GUT.HeeckLeQqqlConvention.orbit.eq_1 => Physics.HeeckLeQqqlConvention.orbit.eq_1
assert_compatible GUT.HeeckLeQqqlConvention.orbit_inverse => Physics.HeeckLeQqqlConvention.orbit_inverse
assert_compatible GUT.HeeckLeQqqlConvention.paperLocal => Physics.HeeckLeQqqlConvention.paperLocal
assert_compatible GUT.HeeckLeQqqlConvention.paperLocal.eq_1 => Physics.HeeckLeQqqlConvention.paperLocal.eq_1
assert_compatible GUT.HeeckLeQqqlConvention.seed => Physics.HeeckLeQqqlConvention.seed
assert_compatible GUT.HeeckLeQqqlConvention.seed.eq_1 => Physics.HeeckLeQqqlConvention.seed.eq_1
assert_compatible GUT.HeeckLeQqqlConvention.seed_alternating_nonzero => Physics.HeeckLeQqqlConvention.seed_alternating_nonzero
assert_compatible GUT.HeeckLeQqqlConvention.seed_components => Physics.HeeckLeQqqlConvention.seed_components
assert_compatible GUT.HeeckLeQqqlConvention.seed_mixed_nonzero => Physics.HeeckLeQqqlConvention.seed_mixed_nonzero
assert_compatible GUT.HeeckLeQqqlConvention.seed_symmetric_nonzero => Physics.HeeckLeQqqlConvention.seed_symmetric_nonzero
assert_compatible GUT.HeeckLeQqqlConvention.source => Physics.HeeckLeQqqlConvention.source
assert_compatible GUT.HeeckLeQqqlConvention.source.eq_1 => Physics.HeeckLeQqqlConvention.source.eq_1
assert_compatible GUT.HeeckLeQqqlConvention.source_apply => Physics.HeeckLeQqqlConvention.source_apply
assert_compatible GUT.HeeckLeQqqlConvention.source_orbit => Physics.HeeckLeQqqlConvention.source_orbit
