import Physics.StandardModel.Operators.Higgs.FourFamilyHiggsContent
import Physics.StandardModel.Operators.DuqlHiggsContent
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.FourFamilyHiggsContent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourFamilyHiggsContent.CombinedSpace => Physics.FourFamilyHiggsContent.CombinedSpace,
  GUT.FourFamilyHiggsContent.CyclicSpace => Physics.FourFamilyHiggsContent.CyclicSpace,
  GUT.FourFamilyHiggsContent.Indices => Physics.FourFamilyHiggsContent.Indices,
  GUT.FourFamilyHiggsContent.Space => Physics.FourFamilyHiggsContent.Space,
  GUT.FourFamilyHiggsContent.all_forbidden_iff => Physics.FourFamilyHiggsContent.all_forbidden_iff,
  GUT.FourFamilyHiggsContent.all_four_forbidden_iff => Physics.FourFamilyHiggsContent.all_four_forbidden_iff,
  GUT.FourFamilyHiggsContent.allowed_iff => Physics.FourFamilyHiggsContent.allowed_iff,
  GUT.FourFamilyHiggsContent.balance_of_nonzero => Physics.FourFamilyHiggsContent.balance_of_nonzero,
  GUT.FourFamilyHiggsContent.base => Physics.FourFamilyHiggsContent.base,
  GUT.FourFamilyHiggsContent.baseEquiv => Physics.FourFamilyHiggsContent.baseEquiv,
  GUT.FourFamilyHiggsContent.base_injective => Physics.FourFamilyHiggsContent.base_injective,
  GUT.FourFamilyHiggsContent.charge_of_nonzero => Physics.FourFamilyHiggsContent.charge_of_nonzero,
  GUT.FourFamilyHiggsContent.combined_cyclic_allowed_iff => Physics.FourFamilyHiggsContent.combined_cyclic_allowed_iff,
  GUT.FourFamilyHiggsContent.combined_cyclic_forbidden_iff => Physics.FourFamilyHiggsContent.combined_cyclic_forbidden_iff,
  GUT.FourFamilyHiggsContent.combined_forbidden_iff => Physics.FourFamilyHiggsContent.combined_forbidden_iff,
  GUT.FourFamilyHiggsContent.combined_mem => Physics.FourFamilyHiggsContent.combined_mem,
  GUT.FourFamilyHiggsContent.dressed => Physics.FourFamilyHiggsContent.dressed,
  GUT.FourFamilyHiggsContent.dressed_nonzero => Physics.FourFamilyHiggsContent.dressed_nonzero,
  GUT.FourFamilyHiggsContent.duql_control => Physics.FourFamilyHiggsContent.duql_control,
  GUT.FourFamilyHiggsContent.family_charge => Physics.FourFamilyHiggsContent.family_charge,
  GUT.FourFamilyHiggsContent.family_hypercharge => Physics.FourFamilyHiggsContent.family_hypercharge,
  GUT.FourFamilyHiggsContent.fermionFlavor => Physics.FourFamilyHiggsContent.fermionFlavor,
  GUT.FourFamilyHiggsContent.forbidden_iff => Physics.FourFamilyHiggsContent.forbidden_iff,
  GUT.FourFamilyHiggsContent.indices_nonempty_iff => Physics.FourFamilyHiggsContent.indices_nonempty_iff,
  GUT.FourFamilyHiggsContent.instDecidableSupport => Physics.FourFamilyHiggsContent.instDecidableSupport,
  GUT.FourFamilyHiggsContent.nonneutral_zero => Physics.FourFamilyHiggsContent.nonneutral_zero,
  GUT.FourFamilyHiggsContent.project => Physics.FourFamilyHiggsContent.project,
  GUT.FourFamilyHiggsContent.project_eq_self => Physics.FourFamilyHiggsContent.project_eq_self,
  GUT.FourFamilyHiggsContent.project_value => Physics.FourFamilyHiggsContent.project_value,
  GUT.FourFamilyHiggsContent.rawDress => Physics.FourFamilyHiggsContent.rawDress,
  GUT.FourFamilyHiggsContent.rawDress_mem => Physics.FourFamilyHiggsContent.rawDress_mem,
  GUT.FourFamilyHiggsContent.rawDress_value => Physics.FourFamilyHiggsContent.rawDress_value,
  GUT.FourFamilyHiggsContent.scalarFlavor => Physics.FourFamilyHiggsContent.scalarFlavor,
  GUT.FourFamilyHiggsContent.signedCharge => Physics.FourFamilyHiggsContent.signedCharge,
  GUT.FourFamilyHiggsContent.support => Physics.FourFamilyHiggsContent.support,
  GUT.FourFamilyHiggsContent.support.eq_1 => Physics.FourFamilyHiggsContent.support.eq_1,
  GUT.FourFamilyHiggsContent.support_stable => Physics.FourFamilyHiggsContent.support_stable,
  GUT.FourFamilyHiggsContent.unequal_zero => Physics.FourFamilyHiggsContent.unequal_zero
]

assert_compatible GUT.FourFamilyHiggsContent.CombinedSpace => Physics.FourFamilyHiggsContent.CombinedSpace
assert_compatible GUT.FourFamilyHiggsContent.CyclicSpace => Physics.FourFamilyHiggsContent.CyclicSpace
assert_compatible GUT.FourFamilyHiggsContent.Indices => Physics.FourFamilyHiggsContent.Indices
assert_compatible GUT.FourFamilyHiggsContent.Space => Physics.FourFamilyHiggsContent.Space
assert_compatible GUT.FourFamilyHiggsContent.all_forbidden_iff => Physics.FourFamilyHiggsContent.all_forbidden_iff
assert_compatible GUT.FourFamilyHiggsContent.all_four_forbidden_iff => Physics.FourFamilyHiggsContent.all_four_forbidden_iff
assert_compatible GUT.FourFamilyHiggsContent.allowed_iff => Physics.FourFamilyHiggsContent.allowed_iff
assert_compatible GUT.FourFamilyHiggsContent.balance_of_nonzero => Physics.FourFamilyHiggsContent.balance_of_nonzero
assert_compatible GUT.FourFamilyHiggsContent.base => Physics.FourFamilyHiggsContent.base
assert_compatible GUT.FourFamilyHiggsContent.baseEquiv => Physics.FourFamilyHiggsContent.baseEquiv
assert_compatible GUT.FourFamilyHiggsContent.base_injective => Physics.FourFamilyHiggsContent.base_injective
assert_compatible GUT.FourFamilyHiggsContent.charge_of_nonzero => Physics.FourFamilyHiggsContent.charge_of_nonzero
assert_compatible GUT.FourFamilyHiggsContent.combined_cyclic_allowed_iff => Physics.FourFamilyHiggsContent.combined_cyclic_allowed_iff
assert_compatible GUT.FourFamilyHiggsContent.combined_cyclic_forbidden_iff => Physics.FourFamilyHiggsContent.combined_cyclic_forbidden_iff
assert_compatible GUT.FourFamilyHiggsContent.combined_forbidden_iff => Physics.FourFamilyHiggsContent.combined_forbidden_iff
assert_compatible GUT.FourFamilyHiggsContent.combined_mem => Physics.FourFamilyHiggsContent.combined_mem
assert_compatible GUT.FourFamilyHiggsContent.dressed => Physics.FourFamilyHiggsContent.dressed
assert_compatible GUT.FourFamilyHiggsContent.dressed_nonzero => Physics.FourFamilyHiggsContent.dressed_nonzero
assert_compatible GUT.FourFamilyHiggsContent.duql_control => Physics.FourFamilyHiggsContent.duql_control
assert_compatible GUT.FourFamilyHiggsContent.family_charge => Physics.FourFamilyHiggsContent.family_charge
assert_compatible GUT.FourFamilyHiggsContent.family_hypercharge => Physics.FourFamilyHiggsContent.family_hypercharge
assert_compatible GUT.FourFamilyHiggsContent.fermionFlavor => Physics.FourFamilyHiggsContent.fermionFlavor
assert_compatible GUT.FourFamilyHiggsContent.forbidden_iff => Physics.FourFamilyHiggsContent.forbidden_iff
assert_compatible GUT.FourFamilyHiggsContent.indices_nonempty_iff => Physics.FourFamilyHiggsContent.indices_nonempty_iff
assert_compatible GUT.FourFamilyHiggsContent.instDecidableSupport => Physics.FourFamilyHiggsContent.instDecidableSupport
assert_compatible GUT.FourFamilyHiggsContent.nonneutral_zero => Physics.FourFamilyHiggsContent.nonneutral_zero
assert_compatible GUT.FourFamilyHiggsContent.project => Physics.FourFamilyHiggsContent.project
assert_compatible GUT.FourFamilyHiggsContent.project_eq_self => Physics.FourFamilyHiggsContent.project_eq_self
assert_compatible GUT.FourFamilyHiggsContent.project_value => Physics.FourFamilyHiggsContent.project_value
assert_compatible GUT.FourFamilyHiggsContent.rawDress => Physics.FourFamilyHiggsContent.rawDress
assert_compatible GUT.FourFamilyHiggsContent.rawDress_mem => Physics.FourFamilyHiggsContent.rawDress_mem
assert_compatible GUT.FourFamilyHiggsContent.rawDress_value => Physics.FourFamilyHiggsContent.rawDress_value
assert_compatible GUT.FourFamilyHiggsContent.scalarFlavor => Physics.FourFamilyHiggsContent.scalarFlavor
assert_compatible GUT.FourFamilyHiggsContent.signedCharge => Physics.FourFamilyHiggsContent.signedCharge
assert_compatible GUT.FourFamilyHiggsContent.support => Physics.FourFamilyHiggsContent.support
assert_compatible GUT.FourFamilyHiggsContent.support.eq_1 => Physics.FourFamilyHiggsContent.support.eq_1
assert_compatible GUT.FourFamilyHiggsContent.support_stable => Physics.FourFamilyHiggsContent.support_stable
assert_compatible GUT.FourFamilyHiggsContent.unequal_zero => Physics.FourFamilyHiggsContent.unequal_zero
