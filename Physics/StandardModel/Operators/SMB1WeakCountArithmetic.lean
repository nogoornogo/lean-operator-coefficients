import Physics.StandardModel.Operators.Support.Dimension.SMB1WeakCountArithmetic
import Physics.StandardModel.Operators.SMB1DimensionBounds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1WeakCountArithmetic instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1WeakCountArithmetic.baryon => Physics.SMB1WeakCountArithmetic.baryon,
  GUT.SMB1WeakCountArithmetic.capacity_sums => Physics.SMB1WeakCountArithmetic.capacity_sums,
  GUT.SMB1WeakCountArithmetic.hypercharge => Physics.SMB1WeakCountArithmetic.hypercharge,
  GUT.SMB1WeakCountArithmetic.lepton => Physics.SMB1WeakCountArithmetic.lepton,
  GUT.SMB1WeakCountArithmetic.total => Physics.SMB1WeakCountArithmetic.total,
  GUT.SMB1WeakCountArithmetic.weak_envelope => Physics.SMB1WeakCountArithmetic.weak_envelope
]

assert_compatible GUT.SMB1WeakCountArithmetic.baryon => Physics.SMB1WeakCountArithmetic.baryon
assert_compatible GUT.SMB1WeakCountArithmetic.capacity_sums => Physics.SMB1WeakCountArithmetic.capacity_sums
assert_compatible GUT.SMB1WeakCountArithmetic.hypercharge => Physics.SMB1WeakCountArithmetic.hypercharge
assert_compatible GUT.SMB1WeakCountArithmetic.lepton => Physics.SMB1WeakCountArithmetic.lepton
assert_compatible GUT.SMB1WeakCountArithmetic.total => Physics.SMB1WeakCountArithmetic.total
assert_compatible GUT.SMB1WeakCountArithmetic.weak_envelope => Physics.SMB1WeakCountArithmetic.weak_envelope
