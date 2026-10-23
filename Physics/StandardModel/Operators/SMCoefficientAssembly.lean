import Physics.StandardModel.Operators.Support.Coordinates.SMCoefficientAssembly
import Physics.StandardModel.Operators.SMGroupedCharacter
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMCoefficientAssembly instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCoefficientAssembly.evaluate => Physics.SMCoefficientAssembly.evaluate,
  GUT.SMCoefficientAssembly.factor => Physics.SMCoefficientAssembly.factor
]

assert_compatible GUT.SMCoefficientAssembly.evaluate => Physics.SMCoefficientAssembly.evaluate
assert_compatible GUT.SMCoefficientAssembly.factor => Physics.SMCoefficientAssembly.factor
