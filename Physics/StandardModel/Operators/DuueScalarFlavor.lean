import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueScalarFlavor
import Physics.StandardModel.Operators.DuueResidualCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueScalarFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuueScalarFlavor.exists_nonzero_iff_charge_trivial => Physics.DuueScalarFlavor.exists_nonzero_iff_charge_trivial,
  GUT.DuueScalarFlavor.oneGenerationEquiv => Physics.DuueScalarFlavor.oneGenerationEquiv,
  GUT.DuueScalarFlavor.oneGeneration_finrank => Physics.DuueScalarFlavor.oneGeneration_finrank,
  GUT.DuueScalarFlavor.scalarCoefficient => Physics.DuueScalarFlavor.scalarCoefficient,
  GUT.DuueScalarFlavor.scalarEquiv => Physics.DuueScalarFlavor.scalarEquiv,
  GUT.DuueScalarFlavor.scalar_formula => Physics.DuueScalarFlavor.scalar_formula
]

assert_compatible GUT.DuueScalarFlavor.exists_nonzero_iff_charge_trivial => Physics.DuueScalarFlavor.exists_nonzero_iff_charge_trivial
assert_compatible GUT.DuueScalarFlavor.oneGenerationEquiv => Physics.DuueScalarFlavor.oneGenerationEquiv
assert_compatible GUT.DuueScalarFlavor.oneGeneration_finrank => Physics.DuueScalarFlavor.oneGeneration_finrank
assert_compatible GUT.DuueScalarFlavor.scalarCoefficient => Physics.DuueScalarFlavor.scalarCoefficient
assert_compatible GUT.DuueScalarFlavor.scalarEquiv => Physics.DuueScalarFlavor.scalarEquiv
assert_compatible GUT.DuueScalarFlavor.scalar_formula => Physics.DuueScalarFlavor.scalar_formula
