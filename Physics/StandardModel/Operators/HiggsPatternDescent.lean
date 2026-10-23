import Physics.StandardModel.Operators.Higgs.HiggsPatternDescent
import Math.RepresentationTheory.TypedSymmetricPatternHom
import Math.RepresentationTheory.TwoBlockSymmetricDescent
import Math.LinearAlgebra.SelectionCriteria
import Physics.StandardModel.Operators.NeutralHiggsPowers
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.HiggsPatternDescent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsPatternDescent.Ordered => Physics.HiggsPatternDescent.Ordered,
  GUT.HiggsPatternDescent.Space => Physics.HiggsPatternDescent.Space,
  GUT.HiggsPatternDescent.allowed_iff => Physics.HiggsPatternDescent.allowed_iff,
  GUT.HiggsPatternDescent.equiv => Physics.HiggsPatternDescent.equiv,
  GUT.HiggsPatternDescent.equiv_apply => Physics.HiggsPatternDescent.equiv_apply,
  GUT.HiggsPatternDescent.forbidden_iff => Physics.HiggsPatternDescent.forbidden_iff,
  GUT.HiggsPatternDescent.source => Physics.HiggsPatternDescent.source
]

assert_compatible GUT.HiggsPatternDescent.Ordered => Physics.HiggsPatternDescent.Ordered
assert_compatible GUT.HiggsPatternDescent.Space => Physics.HiggsPatternDescent.Space
assert_compatible GUT.HiggsPatternDescent.allowed_iff => Physics.HiggsPatternDescent.allowed_iff
assert_compatible GUT.HiggsPatternDescent.equiv => Physics.HiggsPatternDescent.equiv
assert_compatible GUT.HiggsPatternDescent.equiv_apply => Physics.HiggsPatternDescent.equiv_apply
assert_compatible GUT.HiggsPatternDescent.forbidden_iff => Physics.HiggsPatternDescent.forbidden_iff
assert_compatible GUT.HiggsPatternDescent.source => Physics.HiggsPatternDescent.source
