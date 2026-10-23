import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFieldTensor
import Physics.StandardModel.Operators.BnvSevenPatternDescent
import Math.RepresentationTheory.FourTensorLinearSlot
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFieldTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenFieldTensor.evaluateMap => Physics.BnvSevenFieldTensor.evaluateMap,
  GUT.BnvSevenFieldTensor.flavorTensor => Physics.BnvSevenFieldTensor.flavorTensor,
  GUT.BnvSevenFieldTensor.gaugeTensor => Physics.BnvSevenFieldTensor.gaugeTensor,
  GUT.BnvSevenFieldTensor.invariantEquiv => Physics.BnvSevenFieldTensor.invariantEquiv,
  GUT.BnvSevenFieldTensor.localScalar => Physics.BnvSevenFieldTensor.localScalar,
  GUT.BnvSevenFieldTensor.localTensor => Physics.BnvSevenFieldTensor.localTensor,
  GUT.BnvSevenFieldTensor.orderedEquiv => Physics.BnvSevenFieldTensor.orderedEquiv,
  GUT.BnvSevenFieldTensor.regroup => Physics.BnvSevenFieldTensor.regroup,
  GUT.BnvSevenFieldTensor.regroupLocal => Physics.BnvSevenFieldTensor.regroupLocal,
  GUT.BnvSevenFieldTensor.representation => Physics.BnvSevenFieldTensor.representation,
  GUT.BnvSevenFieldTensor.scalarWithSpin => Physics.BnvSevenFieldTensor.scalarWithSpin,
  GUT.BnvSevenFieldTensor.spinTensor => Physics.BnvSevenFieldTensor.spinTensor,
  GUT.BnvSevenFieldTensor.tensorDescent => Physics.BnvSevenFieldTensor.tensorDescent,
  GUT.BnvSevenFieldTensor.tensorSector => Physics.BnvSevenFieldTensor.tensorSector
]

assert_compatible GUT.BnvSevenFieldTensor.evaluateMap => Physics.BnvSevenFieldTensor.evaluateMap
assert_compatible GUT.BnvSevenFieldTensor.flavorTensor => Physics.BnvSevenFieldTensor.flavorTensor
assert_compatible GUT.BnvSevenFieldTensor.gaugeTensor => Physics.BnvSevenFieldTensor.gaugeTensor
assert_compatible GUT.BnvSevenFieldTensor.invariantEquiv => Physics.BnvSevenFieldTensor.invariantEquiv
assert_compatible GUT.BnvSevenFieldTensor.localScalar => Physics.BnvSevenFieldTensor.localScalar
assert_compatible GUT.BnvSevenFieldTensor.localTensor => Physics.BnvSevenFieldTensor.localTensor
assert_compatible GUT.BnvSevenFieldTensor.orderedEquiv => Physics.BnvSevenFieldTensor.orderedEquiv
assert_compatible GUT.BnvSevenFieldTensor.regroup => Physics.BnvSevenFieldTensor.regroup
assert_compatible GUT.BnvSevenFieldTensor.regroupLocal => Physics.BnvSevenFieldTensor.regroupLocal
assert_compatible GUT.BnvSevenFieldTensor.representation => Physics.BnvSevenFieldTensor.representation
assert_compatible GUT.BnvSevenFieldTensor.scalarWithSpin => Physics.BnvSevenFieldTensor.scalarWithSpin
assert_compatible GUT.BnvSevenFieldTensor.spinTensor => Physics.BnvSevenFieldTensor.spinTensor
assert_compatible GUT.BnvSevenFieldTensor.tensorDescent => Physics.BnvSevenFieldTensor.tensorDescent
assert_compatible GUT.BnvSevenFieldTensor.tensorSector => Physics.BnvSevenFieldTensor.tensorSector
