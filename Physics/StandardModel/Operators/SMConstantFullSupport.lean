import Physics.StandardModel.Operators.Support.Coordinates.SMConstantFullSupport
import Physics.StandardModel.Operators.SMQConjugateKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMConstantFullSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMConstantFullSupport.conjugate_lepton_allowed_iff => Physics.SMConstantFullSupport.conjugate_lepton_allowed_iff,
  GUT.SMConstantFullSupport.conjugate_quark_allowed_iff => Physics.SMConstantFullSupport.conjugate_quark_allowed_iff,
  GUT.SMConstantFullSupport.flavor => Physics.SMConstantFullSupport.flavor,
  GUT.SMConstantFullSupport.lepton_allowed_iff => Physics.SMConstantFullSupport.lepton_allowed_iff,
  GUT.SMConstantFullSupport.local_surjective => Physics.SMConstantFullSupport.local_surjective,
  GUT.SMConstantFullSupport.quark_allowed_iff => Physics.SMConstantFullSupport.quark_allowed_iff,
  GUT.SMConstantFullSupport.testEquiv => Physics.SMConstantFullSupport.testEquiv
]

assert_compatible GUT.SMConstantFullSupport.conjugate_lepton_allowed_iff => Physics.SMConstantFullSupport.conjugate_lepton_allowed_iff
assert_compatible GUT.SMConstantFullSupport.conjugate_quark_allowed_iff => Physics.SMConstantFullSupport.conjugate_quark_allowed_iff
assert_compatible GUT.SMConstantFullSupport.flavor => Physics.SMConstantFullSupport.flavor
assert_compatible GUT.SMConstantFullSupport.lepton_allowed_iff => Physics.SMConstantFullSupport.lepton_allowed_iff
assert_compatible GUT.SMConstantFullSupport.local_surjective => Physics.SMConstantFullSupport.local_surjective
assert_compatible GUT.SMConstantFullSupport.quark_allowed_iff => Physics.SMConstantFullSupport.quark_allowed_iff
assert_compatible GUT.SMConstantFullSupport.testEquiv => Physics.SMConstantFullSupport.testEquiv
