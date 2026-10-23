import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlConvention
import Physics.StandardModel.Operators.DuqlExteriorCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiDuqlConvention.fermionic_reorder => Physics.LiDuqlConvention.fermionic_reorder,
  GUT.LiDuqlConvention.paperLocal => Physics.LiDuqlConvention.paperLocal,
  GUT.LiDuqlConvention.paperLocal.eq_1 => Physics.LiDuqlConvention.paperLocal.eq_1,
  GUT.LiDuqlConvention.reorder_parity => Physics.LiDuqlConvention.reorder_parity
]

assert_compatible GUT.LiDuqlConvention.fermionic_reorder => Physics.LiDuqlConvention.fermionic_reorder
assert_compatible GUT.LiDuqlConvention.paperLocal => Physics.LiDuqlConvention.paperLocal
assert_compatible GUT.LiDuqlConvention.paperLocal.eq_1 => Physics.LiDuqlConvention.paperLocal.eq_1
assert_compatible GUT.LiDuqlConvention.reorder_parity => Physics.LiDuqlConvention.reorder_parity
