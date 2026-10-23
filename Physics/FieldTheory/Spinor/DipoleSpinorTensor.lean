import Physics.FieldTheory.Spinor.Tensors.DipoleSpinorTensor
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.TwoComponentContractions
import Math.RepresentationTheory.InvariantEvaluation
import Math.RepresentationTheory.TwoComponentSymmetricSquare
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Tensors.DipoleSpinorTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleSpinorTensor.Strength => Physics.DipoleSpinorTensor.Strength,
  GUT.DipoleSpinorTensor.contraction => Physics.DipoleSpinorTensor.contraction,
  GUT.DipoleSpinorTensor.contraction_tmul => Physics.DipoleSpinorTensor.contraction_tmul,
  GUT.DipoleSpinorTensor.coordinate => Physics.DipoleSpinorTensor.coordinate,
  GUT.DipoleSpinorTensor.coordinate.eq_1 => Physics.DipoleSpinorTensor.coordinate.eq_1,
  GUT.DipoleSpinorTensor.localRepresentation => Physics.DipoleSpinorTensor.localRepresentation,
  GUT.DipoleSpinorTensor.normalized => Physics.DipoleSpinorTensor.normalized,
  GUT.DipoleSpinorTensor.strength => Physics.DipoleSpinorTensor.strength,
  GUT.DipoleSpinorTensor.symmetric => Physics.DipoleSpinorTensor.symmetric,
  GUT.DipoleSpinorTensor.unique => Physics.DipoleSpinorTensor.unique,
  GUT.DipoleSpinorTensor.witness => Physics.DipoleSpinorTensor.witness,
  GUT.DipoleSpinorTensor.witness.eq_1 => Physics.DipoleSpinorTensor.witness.eq_1
]

assert_compatible GUT.DipoleSpinorTensor.Strength => Physics.DipoleSpinorTensor.Strength
assert_compatible GUT.DipoleSpinorTensor.contraction => Physics.DipoleSpinorTensor.contraction
assert_compatible GUT.DipoleSpinorTensor.contraction_tmul => Physics.DipoleSpinorTensor.contraction_tmul
assert_compatible GUT.DipoleSpinorTensor.coordinate => Physics.DipoleSpinorTensor.coordinate
assert_compatible GUT.DipoleSpinorTensor.coordinate.eq_1 => Physics.DipoleSpinorTensor.coordinate.eq_1
assert_compatible GUT.DipoleSpinorTensor.localRepresentation => Physics.DipoleSpinorTensor.localRepresentation
assert_compatible GUT.DipoleSpinorTensor.normalized => Physics.DipoleSpinorTensor.normalized
assert_compatible GUT.DipoleSpinorTensor.strength => Physics.DipoleSpinorTensor.strength
assert_compatible GUT.DipoleSpinorTensor.symmetric => Physics.DipoleSpinorTensor.symmetric
assert_compatible GUT.DipoleSpinorTensor.unique => Physics.DipoleSpinorTensor.unique
assert_compatible GUT.DipoleSpinorTensor.witness => Physics.DipoleSpinorTensor.witness
assert_compatible GUT.DipoleSpinorTensor.witness.eq_1 => Physics.DipoleSpinorTensor.witness.eq_1
