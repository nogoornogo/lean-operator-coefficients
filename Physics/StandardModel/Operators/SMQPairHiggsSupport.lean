import Physics.StandardModel.Operators.Support.Quark.SMQPairHiggsSupport
import Physics.StandardModel.Operators.SMQCoreBranching
import Physics.StandardModel.Operators.SMColoredPairHiggsSupport
import Math.RepresentationTheory.InvariantPairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQPairHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQPairHiggsSupport.color => Physics.SMQPairHiggsSupport.color,
  GUT.SMQPairHiggsSupport.coreCoefficient => Physics.SMQPairHiggsSupport.coreCoefficient,
  GUT.SMQPairHiggsSupport.core_allowed => Physics.SMQPairHiggsSupport.core_allowed,
  GUT.SMQPairHiggsSupport.hypercharge => Physics.SMQPairHiggsSupport.hypercharge,
  GUT.SMQPairHiggsSupport.instAddCommGroupTensorProductComplex_physics => Physics.SMQPairHiggsSupport.instAddCommGroupTensorProductComplex_physics,
  GUT.SMQPairHiggsSupport.local_allowed => Physics.SMQPairHiggsSupport.local_allowed,
  GUT.SMQPairHiggsSupport.local_iff => Physics.SMQPairHiggsSupport.local_iff,
  GUT.SMQPairHiggsSupport.negativeColor => Physics.SMQPairHiggsSupport.negativeColor,
  GUT.SMQPairHiggsSupport.negativeColor_surjective => Physics.SMQPairHiggsSupport.negativeColor_surjective,
  GUT.SMQPairHiggsSupport.original_ql_iff => Physics.SMQPairHiggsSupport.original_ql_iff,
  GUT.SMQPairHiggsSupport.pattern => Physics.SMQPairHiggsSupport.pattern,
  GUT.SMQPairHiggsSupport.positiveColor => Physics.SMQPairHiggsSupport.positiveColor,
  GUT.SMQPairHiggsSupport.positiveColor_surjective => Physics.SMQPairHiggsSupport.positiveColor_surjective,
  GUT.SMQPairHiggsSupport.residual => Physics.SMQPairHiggsSupport.residual,
  GUT.SMQPairHiggsSupport.semisimple_source => Physics.SMQPairHiggsSupport.semisimple_source
]

assert_compatible GUT.SMQPairHiggsSupport.color => Physics.SMQPairHiggsSupport.color
assert_compatible GUT.SMQPairHiggsSupport.coreCoefficient => Physics.SMQPairHiggsSupport.coreCoefficient
assert_compatible GUT.SMQPairHiggsSupport.core_allowed => Physics.SMQPairHiggsSupport.core_allowed
assert_compatible GUT.SMQPairHiggsSupport.hypercharge => Physics.SMQPairHiggsSupport.hypercharge
assert_compatible GUT.SMQPairHiggsSupport.instAddCommGroupTensorProductComplex_physics => Physics.SMQPairHiggsSupport.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMQPairHiggsSupport.local_allowed => Physics.SMQPairHiggsSupport.local_allowed
assert_compatible GUT.SMQPairHiggsSupport.local_iff => Physics.SMQPairHiggsSupport.local_iff
assert_compatible GUT.SMQPairHiggsSupport.negativeColor => Physics.SMQPairHiggsSupport.negativeColor
assert_compatible GUT.SMQPairHiggsSupport.negativeColor_surjective => Physics.SMQPairHiggsSupport.negativeColor_surjective
assert_compatible GUT.SMQPairHiggsSupport.original_ql_iff => Physics.SMQPairHiggsSupport.original_ql_iff
assert_compatible GUT.SMQPairHiggsSupport.pattern => Physics.SMQPairHiggsSupport.pattern
assert_compatible GUT.SMQPairHiggsSupport.positiveColor => Physics.SMQPairHiggsSupport.positiveColor
assert_compatible GUT.SMQPairHiggsSupport.positiveColor_surjective => Physics.SMQPairHiggsSupport.positiveColor_surjective
assert_compatible GUT.SMQPairHiggsSupport.residual => Physics.SMQPairHiggsSupport.residual
assert_compatible GUT.SMQPairHiggsSupport.semisimple_source => Physics.SMQPairHiggsSupport.semisimple_source
