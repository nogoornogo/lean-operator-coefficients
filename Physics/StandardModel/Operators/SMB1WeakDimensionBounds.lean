import Physics.StandardModel.Operators.Support.Dimension.SMB1WeakDimensionBounds
import Physics.StandardModel.Operators.SMB1WeakCountArithmetic
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1WeakDimensionBounds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1WeakCountArithmetic.baryon.eq_1 => Physics.SMB1WeakCountArithmetic.baryon.eq_1,
  GUT.SMB1WeakCountArithmetic.hypercharge.eq_1 => Physics.SMB1WeakCountArithmetic.hypercharge.eq_1,
  GUT.SMB1WeakCountArithmetic.lepton.eq_1 => Physics.SMB1WeakCountArithmetic.lepton.eq_1,
  GUT.SMB1WeakDimensionBounds.counts_baryon => Physics.SMB1WeakDimensionBounds.counts_baryon,
  GUT.SMB1WeakDimensionBounds.counts_hypercharge => Physics.SMB1WeakDimensionBounds.counts_hypercharge,
  GUT.SMB1WeakDimensionBounds.counts_lepton => Physics.SMB1WeakDimensionBounds.counts_lepton,
  GUT.SMB1WeakDimensionBounds.counts_total => Physics.SMB1WeakDimensionBounds.counts_total,
  GUT.SMB1WeakDimensionBounds.original_count_bounds => Physics.SMB1WeakDimensionBounds.original_count_bounds,
  GUT.SMB1WeakDimensionBounds.original_delta_bounds => Physics.SMB1WeakDimensionBounds.original_delta_bounds,
  GUT.SMB1WeakDimensionBounds.original_weak_envelope => Physics.SMB1WeakDimensionBounds.original_weak_envelope,
  GUT.SMChargeDegreeBounds.twiceDimension.eq_1 => Physics.SMChargeDegreeBounds.twiceDimension.eq_1
]

assert_compatible GUT.SMB1WeakCountArithmetic.baryon.eq_1 => Physics.SMB1WeakCountArithmetic.baryon.eq_1
assert_compatible GUT.SMB1WeakCountArithmetic.hypercharge.eq_1 => Physics.SMB1WeakCountArithmetic.hypercharge.eq_1
assert_compatible GUT.SMB1WeakCountArithmetic.lepton.eq_1 => Physics.SMB1WeakCountArithmetic.lepton.eq_1
assert_compatible GUT.SMB1WeakDimensionBounds.counts_baryon => Physics.SMB1WeakDimensionBounds.counts_baryon
assert_compatible GUT.SMB1WeakDimensionBounds.counts_hypercharge => Physics.SMB1WeakDimensionBounds.counts_hypercharge
assert_compatible GUT.SMB1WeakDimensionBounds.counts_lepton => Physics.SMB1WeakDimensionBounds.counts_lepton
assert_compatible GUT.SMB1WeakDimensionBounds.counts_total => Physics.SMB1WeakDimensionBounds.counts_total
assert_compatible GUT.SMB1WeakDimensionBounds.original_count_bounds => Physics.SMB1WeakDimensionBounds.original_count_bounds
assert_compatible GUT.SMB1WeakDimensionBounds.original_delta_bounds => Physics.SMB1WeakDimensionBounds.original_delta_bounds
assert_compatible GUT.SMB1WeakDimensionBounds.original_weak_envelope => Physics.SMB1WeakDimensionBounds.original_weak_envelope
assert_compatible GUT.SMChargeDegreeBounds.twiceDimension.eq_1 => Physics.SMChargeDegreeBounds.twiceDimension.eq_1
