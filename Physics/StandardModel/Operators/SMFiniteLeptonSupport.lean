import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonSupport
import Physics.StandardModel.Operators.SMContentCapacity
import Physics.StandardModel.Operators.SMChargeDegreeBounds
import Physics.StandardModel.Operators.SMLeptonChargeWitnesses
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteLeptonSupport.b1_allowed_iff => Physics.SMFiniteLeptonSupport.b1_allowed_iff,
  GUT.SMFiniteLeptonSupport.b1_b2_iff => Physics.SMFiniteLeptonSupport.b1_b2_iff,
  GUT.SMFiniteLeptonSupport.b1_lepton_bound => Physics.SMFiniteLeptonSupport.b1_lepton_bound,
  GUT.SMFiniteLeptonSupport.b2_allowed_iff => Physics.SMFiniteLeptonSupport.b2_allowed_iff,
  GUT.SMFiniteLeptonSupport.exact_original_iff => Physics.SMFiniteLeptonSupport.exact_original_iff,
  GUT.SMFiniteLeptonSupport.exact_sufficient => Physics.SMFiniteLeptonSupport.exact_sufficient,
  GUT.SMFiniteLeptonSupport.leptonRange => Physics.SMFiniteLeptonSupport.leptonRange,
  GUT.SMFiniteLeptonSupport.leptonRange.eq_1 => Physics.SMFiniteLeptonSupport.leptonRange.eq_1,
  GUT.SMFiniteLeptonSupport.lepton_capacity => Physics.SMFiniteLeptonSupport.lepton_capacity,
  GUT.SMFiniteLeptonSupport.lepton_counts => Physics.SMFiniteLeptonSupport.lepton_counts,
  GUT.SMFiniteLeptonSupport.mem_range => Physics.SMFiniteLeptonSupport.mem_range,
  GUT.SMFiniteLeptonSupport.normalize => Physics.SMFiniteLeptonSupport.normalize,
  GUT.SMFiniteLeptonSupport.original_allowed_iff => Physics.SMFiniteLeptonSupport.original_allowed_iff,
  GUT.SMFiniteLeptonSupport.original_fits => Physics.SMFiniteLeptonSupport.original_fits,
  GUT.SMFiniteLeptonSupport.original_forbidden_iff => Physics.SMFiniteLeptonSupport.original_forbidden_iff,
  GUT.SMFiniteLeptonSupport.original_lepton_capacity => Physics.SMFiniteLeptonSupport.original_lepton_capacity,
  GUT.SMFiniteLeptonSupport.original_necessary => Physics.SMFiniteLeptonSupport.original_necessary,
  GUT.SMFiniteLeptonSupport.original_sufficient => Physics.SMFiniteLeptonSupport.original_sufficient,
  GUT.SMFiniteLeptonSupport.range_card => Physics.SMFiniteLeptonSupport.range_card,
  GUT.SMFiniteLeptonSupport.sum_by_species => Physics.SMFiniteLeptonSupport.sum_by_species
]

assert_compatible GUT.SMFiniteLeptonSupport.b1_allowed_iff => Physics.SMFiniteLeptonSupport.b1_allowed_iff
assert_compatible GUT.SMFiniteLeptonSupport.b1_b2_iff => Physics.SMFiniteLeptonSupport.b1_b2_iff
assert_compatible GUT.SMFiniteLeptonSupport.b1_lepton_bound => Physics.SMFiniteLeptonSupport.b1_lepton_bound
assert_compatible GUT.SMFiniteLeptonSupport.b2_allowed_iff => Physics.SMFiniteLeptonSupport.b2_allowed_iff
assert_compatible GUT.SMFiniteLeptonSupport.exact_original_iff => Physics.SMFiniteLeptonSupport.exact_original_iff
assert_compatible GUT.SMFiniteLeptonSupport.exact_sufficient => Physics.SMFiniteLeptonSupport.exact_sufficient
assert_compatible GUT.SMFiniteLeptonSupport.leptonRange => Physics.SMFiniteLeptonSupport.leptonRange
assert_compatible GUT.SMFiniteLeptonSupport.leptonRange.eq_1 => Physics.SMFiniteLeptonSupport.leptonRange.eq_1
assert_compatible GUT.SMFiniteLeptonSupport.lepton_capacity => Physics.SMFiniteLeptonSupport.lepton_capacity
assert_compatible GUT.SMFiniteLeptonSupport.lepton_counts => Physics.SMFiniteLeptonSupport.lepton_counts
assert_compatible GUT.SMFiniteLeptonSupport.mem_range => Physics.SMFiniteLeptonSupport.mem_range
assert_compatible GUT.SMFiniteLeptonSupport.normalize => Physics.SMFiniteLeptonSupport.normalize
assert_compatible GUT.SMFiniteLeptonSupport.original_allowed_iff => Physics.SMFiniteLeptonSupport.original_allowed_iff
assert_compatible GUT.SMFiniteLeptonSupport.original_fits => Physics.SMFiniteLeptonSupport.original_fits
assert_compatible GUT.SMFiniteLeptonSupport.original_forbidden_iff => Physics.SMFiniteLeptonSupport.original_forbidden_iff
assert_compatible GUT.SMFiniteLeptonSupport.original_lepton_capacity => Physics.SMFiniteLeptonSupport.original_lepton_capacity
assert_compatible GUT.SMFiniteLeptonSupport.original_necessary => Physics.SMFiniteLeptonSupport.original_necessary
assert_compatible GUT.SMFiniteLeptonSupport.original_sufficient => Physics.SMFiniteLeptonSupport.original_sufficient
assert_compatible GUT.SMFiniteLeptonSupport.range_card => Physics.SMFiniteLeptonSupport.range_card
assert_compatible GUT.SMFiniteLeptonSupport.sum_by_species => Physics.SMFiniteLeptonSupport.sum_by_species
