import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlScalarFlavor
import Physics.StandardModel.Operators.QqqlExteriorCompleteness
import Physics.StandardModel.Operators.DuueScalarFlavor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlScalarFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlScalarFlavor.family => Physics.QqqlScalarFlavor.family,
  GUT.QqqlScalarFlavor.family_condition => Physics.QqqlScalarFlavor.family_condition,
  GUT.QqqlScalarFlavor.oneGenerationEquiv => Physics.QqqlScalarFlavor.oneGenerationEquiv,
  GUT.QqqlScalarFlavor.oneGeneration_finrank => Physics.QqqlScalarFlavor.oneGeneration_finrank,
  GUT.QqqlScalarFlavor.pattern => Physics.QqqlScalarFlavor.pattern,
  GUT.QqqlScalarFlavor.pattern.eq_1 => Physics.QqqlScalarFlavor.pattern.eq_1,
  GUT.QqqlScalarFlavor.residualEquiv => Physics.QqqlScalarFlavor.residualEquiv
]

assert_compatible GUT.QqqlScalarFlavor.family => Physics.QqqlScalarFlavor.family
assert_compatible GUT.QqqlScalarFlavor.family_condition => Physics.QqqlScalarFlavor.family_condition
assert_compatible GUT.QqqlScalarFlavor.oneGenerationEquiv => Physics.QqqlScalarFlavor.oneGenerationEquiv
assert_compatible GUT.QqqlScalarFlavor.oneGeneration_finrank => Physics.QqqlScalarFlavor.oneGeneration_finrank
assert_compatible GUT.QqqlScalarFlavor.pattern => Physics.QqqlScalarFlavor.pattern
assert_compatible GUT.QqqlScalarFlavor.pattern.eq_1 => Physics.QqqlScalarFlavor.pattern.eq_1
assert_compatible GUT.QqqlScalarFlavor.residualEquiv => Physics.QqqlScalarFlavor.residualEquiv
