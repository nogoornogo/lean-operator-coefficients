import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenControls
import Physics.StandardModel.Operators.BnvSevenCompleteness
import Physics.StandardModel.Operators.CyclicResidualSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenControls.bit => Physics.BnvSevenControls.bit,
  GUT.BnvSevenControls.bit.eq_1 => Physics.BnvSevenControls.bit.eq_1,
  GUT.BnvSevenControls.degree_forbidden => Physics.BnvSevenControls.degree_forbidden,
  GUT.BnvSevenControls.field_action => Physics.BnvSevenControls.field_action,
  GUT.BnvSevenControls.fullGenerator => Physics.BnvSevenControls.fullGenerator,
  GUT.BnvSevenControls.generator => Physics.BnvSevenControls.generator,
  GUT.BnvSevenControls.generator.eq_1 => Physics.BnvSevenControls.generator.eq_1,
  GUT.BnvSevenControls.neutralFlavor => Physics.BnvSevenControls.neutralFlavor,
  GUT.BnvSevenControls.neutralFlavor.eq_1 => Physics.BnvSevenControls.neutralFlavor.eq_1,
  GUT.BnvSevenControls.parityFlavor => Physics.BnvSevenControls.parityFlavor,
  GUT.BnvSevenControls.parityFlavor.eq_1 => Physics.BnvSevenControls.parityFlavor.eq_1,
  GUT.BnvSevenControls.phase => Physics.BnvSevenControls.phase,
  GUT.BnvSevenControls.phase.eq_1 => Physics.BnvSevenControls.phase.eq_1,
  GUT.BnvSevenControls.phase_cubed_ne_one => Physics.BnvSevenControls.phase_cubed_ne_one,
  GUT.BnvSevenControls.positiveControl => Physics.BnvSevenControls.positiveControl,
  GUT.BnvSevenControls.positiveControl.eq_1 => Physics.BnvSevenControls.positiveControl.eq_1,
  GUT.BnvSevenControls.positiveControl_ne_zero => Physics.BnvSevenControls.positiveControl_ne_zero,
  GUT.BnvSevenControls.quarkParity_forbidden => Physics.BnvSevenControls.quarkParity_forbidden,
  GUT.BnvSevenControls.quark_count => Physics.BnvSevenControls.quark_count,
  GUT.BnvSevenControls.scalarFlavor => Physics.BnvSevenControls.scalarFlavor,
  GUT.BnvSevenControls.scalar_action => Physics.BnvSevenControls.scalar_action,
  GUT.BnvSevenControls.sum_bit => Physics.BnvSevenControls.sum_bit,
  GUT.BnvSevenControls.unitResidual => Physics.BnvSevenControls.unitResidual,
  GUT.BnvSevenControls.unitResidual_ne_zero => Physics.BnvSevenControls.unitResidual_ne_zero,
  GUT.CyclicResidualSelection.flavor.eq_1 => Physics.CyclicResidualSelection.flavor.eq_1,
  GUT.CyclicResidualSelection.signedCharges.eq_1 => Physics.CyclicResidualSelection.signedCharges.eq_1
]

assert_compatible GUT.BnvSevenControls.bit => Physics.BnvSevenControls.bit
assert_compatible GUT.BnvSevenControls.bit.eq_1 => Physics.BnvSevenControls.bit.eq_1
assert_compatible GUT.BnvSevenControls.degree_forbidden => Physics.BnvSevenControls.degree_forbidden
assert_compatible GUT.BnvSevenControls.field_action => Physics.BnvSevenControls.field_action
assert_compatible GUT.BnvSevenControls.fullGenerator => Physics.BnvSevenControls.fullGenerator
assert_compatible GUT.BnvSevenControls.generator => Physics.BnvSevenControls.generator
assert_compatible GUT.BnvSevenControls.generator.eq_1 => Physics.BnvSevenControls.generator.eq_1
assert_compatible GUT.BnvSevenControls.neutralFlavor => Physics.BnvSevenControls.neutralFlavor
assert_compatible GUT.BnvSevenControls.neutralFlavor.eq_1 => Physics.BnvSevenControls.neutralFlavor.eq_1
assert_compatible GUT.BnvSevenControls.parityFlavor => Physics.BnvSevenControls.parityFlavor
assert_compatible GUT.BnvSevenControls.parityFlavor.eq_1 => Physics.BnvSevenControls.parityFlavor.eq_1
assert_compatible GUT.BnvSevenControls.phase => Physics.BnvSevenControls.phase
assert_compatible GUT.BnvSevenControls.phase.eq_1 => Physics.BnvSevenControls.phase.eq_1
assert_compatible GUT.BnvSevenControls.phase_cubed_ne_one => Physics.BnvSevenControls.phase_cubed_ne_one
assert_compatible GUT.BnvSevenControls.positiveControl => Physics.BnvSevenControls.positiveControl
assert_compatible GUT.BnvSevenControls.positiveControl.eq_1 => Physics.BnvSevenControls.positiveControl.eq_1
assert_compatible GUT.BnvSevenControls.positiveControl_ne_zero => Physics.BnvSevenControls.positiveControl_ne_zero
assert_compatible GUT.BnvSevenControls.quarkParity_forbidden => Physics.BnvSevenControls.quarkParity_forbidden
assert_compatible GUT.BnvSevenControls.quark_count => Physics.BnvSevenControls.quark_count
assert_compatible GUT.BnvSevenControls.scalarFlavor => Physics.BnvSevenControls.scalarFlavor
assert_compatible GUT.BnvSevenControls.scalar_action => Physics.BnvSevenControls.scalar_action
assert_compatible GUT.BnvSevenControls.sum_bit => Physics.BnvSevenControls.sum_bit
assert_compatible GUT.BnvSevenControls.unitResidual => Physics.BnvSevenControls.unitResidual
assert_compatible GUT.BnvSevenControls.unitResidual_ne_zero => Physics.BnvSevenControls.unitResidual_ne_zero
assert_compatible GUT.CyclicResidualSelection.flavor.eq_1 => Physics.CyclicResidualSelection.flavor.eq_1
assert_compatible GUT.CyclicResidualSelection.signedCharges.eq_1 => Physics.CyclicResidualSelection.signedCharges.eq_1
