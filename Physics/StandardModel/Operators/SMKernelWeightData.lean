import Physics.StandardModel.Operators.Support.Coordinates.SMKernelWeightData
import Physics.StandardModel.Operators.SMSparseCharacter
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMKernelWeightData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMKernelWeightData.data => Physics.SMKernelWeightData.data,
  GUT.SMKernelWeightData.tables => Physics.SMKernelWeightData.tables,
  GUT.SMKernelWeightData.tables_verified => Physics.SMKernelWeightData.tables_verified,
  GUT.SMKernelWeightData.weights_verified => Physics.SMKernelWeightData.weights_verified
]

assert_compatible GUT.SMKernelWeightData.data => Physics.SMKernelWeightData.data
assert_compatible GUT.SMKernelWeightData.tables => Physics.SMKernelWeightData.tables
assert_compatible GUT.SMKernelWeightData.tables_verified => Physics.SMKernelWeightData.tables_verified
assert_compatible GUT.SMKernelWeightData.weights_verified => Physics.SMKernelWeightData.weights_verified
