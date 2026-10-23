import Physics.StandardModel.Operators.Support.Quark.SMColoredPairHiggsSupport
import Physics.StandardModel.Operators.SMColoredSquarePair
import Physics.StandardModel.Operators.SMGenerationCoefficients
import Physics.StandardModel.Operators.SMLowerHiggsSupport
import Math.RepresentationTheory.BinaryPatternExterior
import Math.RepresentationTheory.GenerationExteriorProjection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMColoredPairHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMColoredPairHiggsSupport.Pairs => Physics.SMColoredPairHiggsSupport.Pairs,
  GUT.SMColoredPairHiggsSupport.field => Physics.SMColoredPairHiggsSupport.field,
  GUT.SMColoredPairHiggsSupport.hypercharge => Physics.SMColoredPairHiggsSupport.hypercharge,
  GUT.SMColoredPairHiggsSupport.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredPairHiggsSupport.instAddCommGroupTensorProductComplex_physics,
  GUT.SMColoredPairHiggsSupport.local_allowed => Physics.SMColoredPairHiggsSupport.local_allowed,
  GUT.SMColoredPairHiggsSupport.local_iff => Physics.SMColoredPairHiggsSupport.local_iff,
  GUT.SMColoredPairHiggsSupport.original_ql_iff => Physics.SMColoredPairHiggsSupport.original_ql_iff,
  GUT.SMColoredPairHiggsSupport.pattern => Physics.SMColoredPairHiggsSupport.pattern,
  GUT.SMColoredPairHiggsSupport.residual => Physics.SMColoredPairHiggsSupport.residual,
  GUT.SMColoredPairHiggsSupport.semisimple_source => Physics.SMColoredPairHiggsSupport.semisimple_source,
  GUT.SMColoredPairHiggsSupport.source => Physics.SMColoredPairHiggsSupport.source,
  GUT.SMColoredPairHiggsSupport.sourceEquiv => Physics.SMColoredPairHiggsSupport.sourceEquiv,
  GUT.SMColoredPairHiggsSupport.zeroBosonEquiv => Physics.SMColoredPairHiggsSupport.zeroBosonEquiv
]

assert_compatible GUT.SMColoredPairHiggsSupport.Pairs => Physics.SMColoredPairHiggsSupport.Pairs
assert_compatible GUT.SMColoredPairHiggsSupport.field => Physics.SMColoredPairHiggsSupport.field
assert_compatible GUT.SMColoredPairHiggsSupport.hypercharge => Physics.SMColoredPairHiggsSupport.hypercharge
assert_compatible GUT.SMColoredPairHiggsSupport.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredPairHiggsSupport.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMColoredPairHiggsSupport.local_allowed => Physics.SMColoredPairHiggsSupport.local_allowed
assert_compatible GUT.SMColoredPairHiggsSupport.local_iff => Physics.SMColoredPairHiggsSupport.local_iff
assert_compatible GUT.SMColoredPairHiggsSupport.original_ql_iff => Physics.SMColoredPairHiggsSupport.original_ql_iff
assert_compatible GUT.SMColoredPairHiggsSupport.pattern => Physics.SMColoredPairHiggsSupport.pattern
assert_compatible GUT.SMColoredPairHiggsSupport.residual => Physics.SMColoredPairHiggsSupport.residual
assert_compatible GUT.SMColoredPairHiggsSupport.semisimple_source => Physics.SMColoredPairHiggsSupport.semisimple_source
assert_compatible GUT.SMColoredPairHiggsSupport.source => Physics.SMColoredPairHiggsSupport.source
assert_compatible GUT.SMColoredPairHiggsSupport.sourceEquiv => Physics.SMColoredPairHiggsSupport.sourceEquiv
assert_compatible GUT.SMColoredPairHiggsSupport.zeroBosonEquiv => Physics.SMColoredPairHiggsSupport.zeroBosonEquiv
