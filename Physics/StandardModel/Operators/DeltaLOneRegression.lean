import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneRegression
import Physics.StandardModel.Operators.DeltaLOneInputTransport
import Physics.StandardModel.Operators.QqqlScalarFlavor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneRegression instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaLOneRegression.neutralFlavor => Physics.DeltaLOneRegression.neutralFlavor,
  GUT.DeltaLOneRegression.neutralFlavor.eq_1 => Physics.DeltaLOneRegression.neutralFlavor.eq_1,
  GUT.DeltaLOneRegression.neutralResidualEquiv => Physics.DeltaLOneRegression.neutralResidualEquiv,
  GUT.DeltaLOneRegression.oneGenerationEquiv => Physics.DeltaLOneRegression.oneGenerationEquiv,
  GUT.DeltaLOneRegression.oneGeneration_finrank => Physics.DeltaLOneRegression.oneGeneration_finrank,
  GUT.DeltaLOneRegression.qqueScalarForget => Physics.DeltaLOneRegression.qqueScalarForget,
  GUT.DeltaLOneRegression.qque_scalar_symmetric => Physics.DeltaLOneRegression.qque_scalar_symmetric,
  GUT.DeltaLOneRegression.scalarHom_vanish => Physics.DeltaLOneRegression.scalarHom_vanish,
  GUT.DeltaLOneRegression.scalar_charge_vanish => Physics.DeltaLOneRegression.scalar_charge_vanish,
  GUT.DeltaLOneRegression.zero_quark_factors => Physics.DeltaLOneRegression.zero_quark_factors,
  GUT.DeltaLOneRegression.zero_quark_up => Physics.DeltaLOneRegression.zero_quark_up
]

assert_compatible GUT.DeltaLOneRegression.neutralFlavor => Physics.DeltaLOneRegression.neutralFlavor
assert_compatible GUT.DeltaLOneRegression.neutralFlavor.eq_1 => Physics.DeltaLOneRegression.neutralFlavor.eq_1
assert_compatible GUT.DeltaLOneRegression.neutralResidualEquiv => Physics.DeltaLOneRegression.neutralResidualEquiv
assert_compatible GUT.DeltaLOneRegression.oneGenerationEquiv => Physics.DeltaLOneRegression.oneGenerationEquiv
assert_compatible GUT.DeltaLOneRegression.oneGeneration_finrank => Physics.DeltaLOneRegression.oneGeneration_finrank
assert_compatible GUT.DeltaLOneRegression.qqueScalarForget => Physics.DeltaLOneRegression.qqueScalarForget
assert_compatible GUT.DeltaLOneRegression.qque_scalar_symmetric => Physics.DeltaLOneRegression.qque_scalar_symmetric
assert_compatible GUT.DeltaLOneRegression.scalarHom_vanish => Physics.DeltaLOneRegression.scalarHom_vanish
assert_compatible GUT.DeltaLOneRegression.scalar_charge_vanish => Physics.DeltaLOneRegression.scalar_charge_vanish
assert_compatible GUT.DeltaLOneRegression.zero_quark_factors => Physics.DeltaLOneRegression.zero_quark_factors
assert_compatible GUT.DeltaLOneRegression.zero_quark_up => Physics.DeltaLOneRegression.zero_quark_up
