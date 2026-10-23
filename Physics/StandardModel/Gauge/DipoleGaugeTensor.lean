import Physics.StandardModel.Gauge.Tensors.DipoleGaugeTensor
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.RepresentationTheory.TwoComponentContractions
import Math.RepresentationTheory.InvariantEvaluation
import Math.RepresentationTheory.TwoComponentAdjoint
import Math.RepresentationTheory.TwoComponentTripletDual
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.DipoleGaugeTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleGaugeTensor.adjoint => Physics.DipoleGaugeTensor.adjoint,
  GUT.DipoleGaugeTensor.coordinate => Physics.DipoleGaugeTensor.coordinate,
  GUT.DipoleGaugeTensor.coordinate.eq_1 => Physics.DipoleGaugeTensor.coordinate.eq_1,
  GUT.DipoleGaugeTensor.fromDual => Physics.DipoleGaugeTensor.fromDual,
  GUT.DipoleGaugeTensor.fromDual.eq_1 => Physics.DipoleGaugeTensor.fromDual.eq_1,
  GUT.DipoleGaugeTensor.phases => Physics.DipoleGaugeTensor.phases,
  GUT.DipoleGaugeTensor.singlet => Physics.DipoleGaugeTensor.singlet,
  GUT.DipoleGaugeTensor.singletRepresentation => Physics.DipoleGaugeTensor.singletRepresentation,
  GUT.DipoleGaugeTensor.singletWitness => Physics.DipoleGaugeTensor.singletWitness,
  GUT.DipoleGaugeTensor.singletWitness.eq_1 => Physics.DipoleGaugeTensor.singletWitness.eq_1,
  GUT.DipoleGaugeTensor.singlet_normalized => Physics.DipoleGaugeTensor.singlet_normalized,
  GUT.DipoleGaugeTensor.singlet_tmul => Physics.DipoleGaugeTensor.singlet_tmul,
  GUT.DipoleGaugeTensor.singlet_unique => Physics.DipoleGaugeTensor.singlet_unique,
  GUT.DipoleGaugeTensor.toDual => Physics.DipoleGaugeTensor.toDual,
  GUT.DipoleGaugeTensor.tripletContraction => Physics.DipoleGaugeTensor.tripletContraction,
  GUT.DipoleGaugeTensor.tripletRepresentation => Physics.DipoleGaugeTensor.tripletRepresentation,
  GUT.DipoleGaugeTensor.tripletWitness => Physics.DipoleGaugeTensor.tripletWitness,
  GUT.DipoleGaugeTensor.tripletWitness.eq_1 => Physics.DipoleGaugeTensor.tripletWitness.eq_1,
  GUT.DipoleGaugeTensor.triplet_normalized => Physics.DipoleGaugeTensor.triplet_normalized,
  GUT.DipoleGaugeTensor.triplet_tmul => Physics.DipoleGaugeTensor.triplet_tmul,
  GUT.DipoleGaugeTensor.triplet_unique => Physics.DipoleGaugeTensor.triplet_unique,
  GUT.DipoleGaugeTensor.weak => Physics.DipoleGaugeTensor.weak,
  GUT.DipoleGaugeTensor.weakDualEquiv => Physics.DipoleGaugeTensor.weakDualEquiv
]

assert_compatible GUT.DipoleGaugeTensor.adjoint => Physics.DipoleGaugeTensor.adjoint
assert_compatible GUT.DipoleGaugeTensor.coordinate => Physics.DipoleGaugeTensor.coordinate
assert_compatible GUT.DipoleGaugeTensor.coordinate.eq_1 => Physics.DipoleGaugeTensor.coordinate.eq_1
assert_compatible GUT.DipoleGaugeTensor.fromDual => Physics.DipoleGaugeTensor.fromDual
assert_compatible GUT.DipoleGaugeTensor.fromDual.eq_1 => Physics.DipoleGaugeTensor.fromDual.eq_1
assert_compatible GUT.DipoleGaugeTensor.phases => Physics.DipoleGaugeTensor.phases
assert_compatible GUT.DipoleGaugeTensor.singlet => Physics.DipoleGaugeTensor.singlet
assert_compatible GUT.DipoleGaugeTensor.singletRepresentation => Physics.DipoleGaugeTensor.singletRepresentation
assert_compatible GUT.DipoleGaugeTensor.singletWitness => Physics.DipoleGaugeTensor.singletWitness
assert_compatible GUT.DipoleGaugeTensor.singletWitness.eq_1 => Physics.DipoleGaugeTensor.singletWitness.eq_1
assert_compatible GUT.DipoleGaugeTensor.singlet_normalized => Physics.DipoleGaugeTensor.singlet_normalized
assert_compatible GUT.DipoleGaugeTensor.singlet_tmul => Physics.DipoleGaugeTensor.singlet_tmul
assert_compatible GUT.DipoleGaugeTensor.singlet_unique => Physics.DipoleGaugeTensor.singlet_unique
assert_compatible GUT.DipoleGaugeTensor.toDual => Physics.DipoleGaugeTensor.toDual
assert_compatible GUT.DipoleGaugeTensor.tripletContraction => Physics.DipoleGaugeTensor.tripletContraction
assert_compatible GUT.DipoleGaugeTensor.tripletRepresentation => Physics.DipoleGaugeTensor.tripletRepresentation
assert_compatible GUT.DipoleGaugeTensor.tripletWitness => Physics.DipoleGaugeTensor.tripletWitness
assert_compatible GUT.DipoleGaugeTensor.tripletWitness.eq_1 => Physics.DipoleGaugeTensor.tripletWitness.eq_1
assert_compatible GUT.DipoleGaugeTensor.triplet_normalized => Physics.DipoleGaugeTensor.triplet_normalized
assert_compatible GUT.DipoleGaugeTensor.triplet_tmul => Physics.DipoleGaugeTensor.triplet_tmul
assert_compatible GUT.DipoleGaugeTensor.triplet_unique => Physics.DipoleGaugeTensor.triplet_unique
assert_compatible GUT.DipoleGaugeTensor.weak => Physics.DipoleGaugeTensor.weak
assert_compatible GUT.DipoleGaugeTensor.weakDualEquiv => Physics.DipoleGaugeTensor.weakDualEquiv
