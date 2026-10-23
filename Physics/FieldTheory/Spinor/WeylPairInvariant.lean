import Physics.FieldTheory.Spinor.Tensors.WeylPairInvariant
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Math.RepresentationTheory.TwoComponentContractions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Tensors.WeylPairInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylPairInvariant.Coefficient => Physics.WeylPairInvariant.Coefficient,
  GUT.WeylPairInvariant.apply_formula => Physics.WeylPairInvariant.apply_formula,
  GUT.WeylPairInvariant.coordinateEquiv => Physics.WeylPairInvariant.coordinateEquiv,
  GUT.WeylPairInvariant.epsilon_witness => Physics.WeylPairInvariant.epsilon_witness,
  GUT.WeylPairInvariant.nonzero_iff => Physics.WeylPairInvariant.nonzero_iff,
  GUT.WeylPairInvariant.unique => Physics.WeylPairInvariant.unique,
  GUT.WeylPairInvariant.witness => Physics.WeylPairInvariant.witness
]

assert_compatible GUT.WeylPairInvariant.Coefficient => Physics.WeylPairInvariant.Coefficient
assert_compatible GUT.WeylPairInvariant.apply_formula => Physics.WeylPairInvariant.apply_formula
assert_compatible GUT.WeylPairInvariant.coordinateEquiv => Physics.WeylPairInvariant.coordinateEquiv
assert_compatible GUT.WeylPairInvariant.epsilon_witness => Physics.WeylPairInvariant.epsilon_witness
assert_compatible GUT.WeylPairInvariant.nonzero_iff => Physics.WeylPairInvariant.nonzero_iff
assert_compatible GUT.WeylPairInvariant.unique => Physics.WeylPairInvariant.unique
assert_compatible GUT.WeylPairInvariant.witness => Physics.WeylPairInvariant.witness
