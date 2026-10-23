import Physics.StandardModel.Operators.Support.Coordinates.SMContentCapacity
import Physics.StandardModel.Operators.SMMixedWeakCapacity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMContentCapacity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMContentCapacity.Fits => Physics.SMContentCapacity.Fits,
  GUT.SMContentCapacity.Fits.eq_1 => Physics.SMContentCapacity.Fits.eq_1,
  GUT.SMContentCapacity.fieldFinite => Physics.SMContentCapacity.fieldFinite,
  GUT.SMContentCapacity.local_forbidden => Physics.SMContentCapacity.local_forbidden,
  GUT.SMContentCapacity.original_ql_forbidden => Physics.SMContentCapacity.original_ql_forbidden,
  GUT.SMContentCapacity.sourceFinite => Physics.SMContentCapacity.sourceFinite,
  GUT.SMContentCapacity.source_allowed_iff => Physics.SMContentCapacity.source_allowed_iff,
  GUT.SMContentCapacity.source_finrank_zero => Physics.SMContentCapacity.source_finrank_zero
]

assert_compatible GUT.SMContentCapacity.Fits => Physics.SMContentCapacity.Fits
assert_compatible GUT.SMContentCapacity.Fits.eq_1 => Physics.SMContentCapacity.Fits.eq_1
assert_compatible GUT.SMContentCapacity.fieldFinite => Physics.SMContentCapacity.fieldFinite
assert_compatible GUT.SMContentCapacity.local_forbidden => Physics.SMContentCapacity.local_forbidden
assert_compatible GUT.SMContentCapacity.original_ql_forbidden => Physics.SMContentCapacity.original_ql_forbidden
assert_compatible GUT.SMContentCapacity.sourceFinite => Physics.SMContentCapacity.sourceFinite
assert_compatible GUT.SMContentCapacity.source_allowed_iff => Physics.SMContentCapacity.source_allowed_iff
assert_compatible GUT.SMContentCapacity.source_finrank_zero => Physics.SMContentCapacity.source_finrank_zero
