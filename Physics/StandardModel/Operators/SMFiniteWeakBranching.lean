import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteWeakBranching
import Physics.StandardModel.Operators.SMFiniteConstituentSupport
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Math.RepresentationTheory.SU2FiniteBranching
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteWeakBranching instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteWeakBranching.certificate => Physics.SMFiniteWeakBranching.certificate,
  GUT.SMFiniteWeakBranching.constantCertificate => Physics.SMFiniteWeakBranching.constantCertificate,
  GUT.SMFiniteWeakBranching.constant_bounded => Physics.SMFiniteWeakBranching.constant_bounded,
  GUT.SMFiniteWeakBranching.continuousInclusion => Physics.SMFiniteWeakBranching.continuousInclusion,
  GUT.SMFiniteWeakBranching.inclusion => Physics.SMFiniteWeakBranching.inclusion,
  GUT.SMFiniteWeakBranching.inclusion_continuous => Physics.SMFiniteWeakBranching.inclusion_continuous,
  GUT.SMFiniteWeakBranching.modelEquiv => Physics.SMFiniteWeakBranching.modelEquiv,
  GUT.SMFiniteWeakBranching.source => Physics.SMFiniteWeakBranching.source,
  GUT.SMFiniteWeakBranching.source_bounded => Physics.SMFiniteWeakBranching.source_bounded,
  GUT.SMFiniteWeakBranching.source_continuous => Physics.SMFiniteWeakBranching.source_continuous,
  GUT.SMFiniteWeakBranching.source_restrict => Physics.SMFiniteWeakBranching.source_restrict
]

assert_compatible GUT.SMFiniteWeakBranching.certificate => Physics.SMFiniteWeakBranching.certificate
assert_compatible GUT.SMFiniteWeakBranching.constantCertificate => Physics.SMFiniteWeakBranching.constantCertificate
assert_compatible GUT.SMFiniteWeakBranching.constant_bounded => Physics.SMFiniteWeakBranching.constant_bounded
assert_compatible GUT.SMFiniteWeakBranching.continuousInclusion => Physics.SMFiniteWeakBranching.continuousInclusion
assert_compatible GUT.SMFiniteWeakBranching.inclusion => Physics.SMFiniteWeakBranching.inclusion
assert_compatible GUT.SMFiniteWeakBranching.inclusion_continuous => Physics.SMFiniteWeakBranching.inclusion_continuous
assert_compatible GUT.SMFiniteWeakBranching.modelEquiv => Physics.SMFiniteWeakBranching.modelEquiv
assert_compatible GUT.SMFiniteWeakBranching.source => Physics.SMFiniteWeakBranching.source
assert_compatible GUT.SMFiniteWeakBranching.source_bounded => Physics.SMFiniteWeakBranching.source_bounded
assert_compatible GUT.SMFiniteWeakBranching.source_continuous => Physics.SMFiniteWeakBranching.source_continuous
assert_compatible GUT.SMFiniteWeakBranching.source_restrict => Physics.SMFiniteWeakBranching.source_restrict
