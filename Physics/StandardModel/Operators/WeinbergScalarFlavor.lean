import Physics.StandardModel.Operators.Weinberg.WeinbergScalarFlavor
import Physics.StandardModel.Operators.WeinbergMajorana
import Physics.FieldTheory.Mass.WeylMassTwoTorsion
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergScalarFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial => Physics.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial,
  GUT.WeinbergScalarFlavor.oneGenerationEquiv => Physics.WeinbergScalarFlavor.oneGenerationEquiv,
  GUT.WeinbergScalarFlavor.oneGeneration_finrank => Physics.WeinbergScalarFlavor.oneGeneration_finrank,
  GUT.WeinbergScalarFlavor.scalarCoefficient => Physics.WeinbergScalarFlavor.scalarCoefficient,
  GUT.WeinbergScalarFlavor.scalarEquiv => Physics.WeinbergScalarFlavor.scalarEquiv,
  GUT.WeinbergScalarFlavor.scalar_formula => Physics.WeinbergScalarFlavor.scalar_formula,
  GUT.WeinbergScalarFlavor.sign_allowed => Physics.WeinbergScalarFlavor.sign_allowed
]

assert_compatible GUT.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial => Physics.WeinbergScalarFlavor.exists_nonzero_iff_square_trivial
assert_compatible GUT.WeinbergScalarFlavor.oneGenerationEquiv => Physics.WeinbergScalarFlavor.oneGenerationEquiv
assert_compatible GUT.WeinbergScalarFlavor.oneGeneration_finrank => Physics.WeinbergScalarFlavor.oneGeneration_finrank
assert_compatible GUT.WeinbergScalarFlavor.scalarCoefficient => Physics.WeinbergScalarFlavor.scalarCoefficient
assert_compatible GUT.WeinbergScalarFlavor.scalarEquiv => Physics.WeinbergScalarFlavor.scalarEquiv
assert_compatible GUT.WeinbergScalarFlavor.scalar_formula => Physics.WeinbergScalarFlavor.scalar_formula
assert_compatible GUT.WeinbergScalarFlavor.sign_allowed => Physics.WeinbergScalarFlavor.sign_allowed
