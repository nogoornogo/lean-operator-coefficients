import Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlConvention
import Physics.StandardModel.Operators.QqqlFlavorComponents
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiQqqlConvention.fermionic_reorder => Physics.LiQqqlConvention.fermionic_reorder,
  GUT.LiQqqlConvention.orbit => Physics.LiQqqlConvention.orbit,
  GUT.LiQqqlConvention.orbit.eq_1 => Physics.LiQqqlConvention.orbit.eq_1,
  GUT.LiQqqlConvention.orbit_inverse => Physics.LiQqqlConvention.orbit_inverse,
  GUT.LiQqqlConvention.paperLocal => Physics.LiQqqlConvention.paperLocal,
  GUT.LiQqqlConvention.paperLocal.eq_1 => Physics.LiQqqlConvention.paperLocal.eq_1,
  GUT.LiQqqlConvention.seed => Physics.LiQqqlConvention.seed,
  GUT.LiQqqlConvention.seed.eq_1 => Physics.LiQqqlConvention.seed.eq_1,
  GUT.LiQqqlConvention.seed_alternating_nonzero => Physics.LiQqqlConvention.seed_alternating_nonzero,
  GUT.LiQqqlConvention.seed_components => Physics.LiQqqlConvention.seed_components,
  GUT.LiQqqlConvention.seed_mixed_nonzero => Physics.LiQqqlConvention.seed_mixed_nonzero,
  GUT.LiQqqlConvention.seed_symmetric_nonzero => Physics.LiQqqlConvention.seed_symmetric_nonzero,
  GUT.LiQqqlConvention.source => Physics.LiQqqlConvention.source,
  GUT.LiQqqlConvention.source.eq_1 => Physics.LiQqqlConvention.source.eq_1,
  GUT.LiQqqlConvention.source_apply => Physics.LiQqqlConvention.source_apply,
  GUT.LiQqqlConvention.source_orbit => Physics.LiQqqlConvention.source_orbit
]

assert_compatible GUT.LiQqqlConvention.fermionic_reorder => Physics.LiQqqlConvention.fermionic_reorder
assert_compatible GUT.LiQqqlConvention.orbit => Physics.LiQqqlConvention.orbit
assert_compatible GUT.LiQqqlConvention.orbit.eq_1 => Physics.LiQqqlConvention.orbit.eq_1
assert_compatible GUT.LiQqqlConvention.orbit_inverse => Physics.LiQqqlConvention.orbit_inverse
assert_compatible GUT.LiQqqlConvention.paperLocal => Physics.LiQqqlConvention.paperLocal
assert_compatible GUT.LiQqqlConvention.paperLocal.eq_1 => Physics.LiQqqlConvention.paperLocal.eq_1
assert_compatible GUT.LiQqqlConvention.seed => Physics.LiQqqlConvention.seed
assert_compatible GUT.LiQqqlConvention.seed.eq_1 => Physics.LiQqqlConvention.seed.eq_1
assert_compatible GUT.LiQqqlConvention.seed_alternating_nonzero => Physics.LiQqqlConvention.seed_alternating_nonzero
assert_compatible GUT.LiQqqlConvention.seed_components => Physics.LiQqqlConvention.seed_components
assert_compatible GUT.LiQqqlConvention.seed_mixed_nonzero => Physics.LiQqqlConvention.seed_mixed_nonzero
assert_compatible GUT.LiQqqlConvention.seed_symmetric_nonzero => Physics.LiQqqlConvention.seed_symmetric_nonzero
assert_compatible GUT.LiQqqlConvention.source => Physics.LiQqqlConvention.source
assert_compatible GUT.LiQqqlConvention.source.eq_1 => Physics.LiQqqlConvention.source.eq_1
assert_compatible GUT.LiQqqlConvention.source_apply => Physics.LiQqqlConvention.source_apply
assert_compatible GUT.LiQqqlConvention.source_orbit => Physics.LiQqqlConvention.source_orbit
