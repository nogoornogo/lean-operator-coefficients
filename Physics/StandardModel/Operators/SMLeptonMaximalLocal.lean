import Physics.StandardModel.Operators.Support.Lepton.SMLeptonMaximalLocal
import Physics.StandardModel.Operators.SMLeptonCoreBranching
import Physics.StandardModel.Operators.SMSignedHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLeptonMaximalLocal instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLeptonMaximalLocal.instAddCommGroupPairCarrier_physics => Physics.SMLeptonMaximalLocal.instAddCommGroupPairCarrier_physics,
  GUT.SMLeptonMaximalLocal.negative => Physics.SMLeptonMaximalLocal.negative,
  GUT.SMLeptonMaximalLocal.positive => Physics.SMLeptonMaximalLocal.positive,
  GUT.SMLeptonMaximalLocal.weakEquiv => Physics.SMLeptonMaximalLocal.weakEquiv
]

assert_compatible GUT.SMLeptonMaximalLocal.instAddCommGroupPairCarrier_physics => Physics.SMLeptonMaximalLocal.instAddCommGroupPairCarrier_physics
assert_compatible GUT.SMLeptonMaximalLocal.negative => Physics.SMLeptonMaximalLocal.negative
assert_compatible GUT.SMLeptonMaximalLocal.positive => Physics.SMLeptonMaximalLocal.positive
assert_compatible GUT.SMLeptonMaximalLocal.weakEquiv => Physics.SMLeptonMaximalLocal.weakEquiv
