import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvZeroBosonBridge
import Physics.StandardModel.Operators.BnvMixedInput
import Physics.StandardModel.Operators.BnvMixedWeylSupport
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvZeroBosonBridge instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvZeroBosonBridge.admissible => Physics.BnvZeroBosonBridge.admissible,
  GUT.BnvZeroBosonBridge.coefficientEquiv => Physics.BnvZeroBosonBridge.coefficientEquiv,
  GUT.BnvZeroBosonBridge.equiv => Physics.BnvZeroBosonBridge.equiv,
  GUT.BnvZeroBosonBridge.extraction => Physics.BnvZeroBosonBridge.extraction,
  GUT.BnvZeroBosonBridge.lepton_support => Physics.BnvZeroBosonBridge.lepton_support,
  GUT.BnvZeroBosonBridge.signedBnv => Physics.BnvZeroBosonBridge.signedBnv
]

assert_compatible GUT.BnvZeroBosonBridge.admissible => Physics.BnvZeroBosonBridge.admissible
assert_compatible GUT.BnvZeroBosonBridge.coefficientEquiv => Physics.BnvZeroBosonBridge.coefficientEquiv
assert_compatible GUT.BnvZeroBosonBridge.equiv => Physics.BnvZeroBosonBridge.equiv
assert_compatible GUT.BnvZeroBosonBridge.extraction => Physics.BnvZeroBosonBridge.extraction
assert_compatible GUT.BnvZeroBosonBridge.lepton_support => Physics.BnvZeroBosonBridge.lepton_support
assert_compatible GUT.BnvZeroBosonBridge.signedBnv => Physics.BnvZeroBosonBridge.signedBnv
