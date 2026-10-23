import Physics.StandardModel.Operators.Weinberg.LiWeinbergConvention
import Physics.StandardModel.Operators.WeinbergResidualHom
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.LiWeinbergConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiWeinbergConvention.diagonal_local => Physics.LiWeinbergConvention.diagonal_local,
  GUT.LiWeinbergConvention.higgs_exchange => Physics.LiWeinbergConvention.higgs_exchange,
  GUT.LiWeinbergConvention.lepton_exchange => Physics.LiWeinbergConvention.lepton_exchange,
  GUT.LiWeinbergConvention.mixed_probe => Physics.LiWeinbergConvention.mixed_probe,
  GUT.LiWeinbergConvention.paperLocal => Physics.LiWeinbergConvention.paperLocal,
  GUT.LiWeinbergConvention.paperLocal.eq_1 => Physics.LiWeinbergConvention.paperLocal.eq_1,
  GUT.LiWeinbergConvention.polarizedLocal => Physics.LiWeinbergConvention.polarizedLocal,
  GUT.LiWeinbergConvention.polarizedLocal.eq_1 => Physics.LiWeinbergConvention.polarizedLocal.eq_1
]

assert_compatible GUT.LiWeinbergConvention.diagonal_local => Physics.LiWeinbergConvention.diagonal_local
assert_compatible GUT.LiWeinbergConvention.higgs_exchange => Physics.LiWeinbergConvention.higgs_exchange
assert_compatible GUT.LiWeinbergConvention.lepton_exchange => Physics.LiWeinbergConvention.lepton_exchange
assert_compatible GUT.LiWeinbergConvention.mixed_probe => Physics.LiWeinbergConvention.mixed_probe
assert_compatible GUT.LiWeinbergConvention.paperLocal => Physics.LiWeinbergConvention.paperLocal
assert_compatible GUT.LiWeinbergConvention.paperLocal.eq_1 => Physics.LiWeinbergConvention.paperLocal.eq_1
assert_compatible GUT.LiWeinbergConvention.polarizedLocal => Physics.LiWeinbergConvention.polarizedLocal
assert_compatible GUT.LiWeinbergConvention.polarizedLocal.eq_1 => Physics.LiWeinbergConvention.polarizedLocal.eq_1
