import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlOrderedCompleteness
import Physics.StandardModel.Gauge.DuqlGaugeUniqueness
import Physics.FieldTheory.Spinor.WeylSpinorUniqueness
import Math.RepresentationTheory.NormalizedInvariantFactor
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlOrderedCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuqlOrderedCompleteness.Coefficient => Physics.DuqlOrderedCompleteness.Coefficient,
  GUT.DuqlOrderedCompleteness.Residual => Physics.DuqlOrderedCompleteness.Residual,
  GUT.DuqlOrderedCompleteness.downSpin => Physics.DuqlOrderedCompleteness.downSpin,
  GUT.DuqlOrderedCompleteness.exists_nonzero_iff => Physics.DuqlOrderedCompleteness.exists_nonzero_iff,
  GUT.DuqlOrderedCompleteness.fields => Physics.DuqlOrderedCompleteness.fields,
  GUT.DuqlOrderedCompleteness.flavor => Physics.DuqlOrderedCompleteness.flavor,
  GUT.DuqlOrderedCompleteness.homEquiv => Physics.DuqlOrderedCompleteness.homEquiv,
  GUT.DuqlOrderedCompleteness.leptonSpin => Physics.DuqlOrderedCompleteness.leptonSpin,
  GUT.DuqlOrderedCompleteness.localContraction => Physics.DuqlOrderedCompleteness.localContraction,
  GUT.DuqlOrderedCompleteness.localContraction.eq_1 => Physics.DuqlOrderedCompleteness.localContraction.eq_1,
  GUT.DuqlOrderedCompleteness.localRegroup => Physics.DuqlOrderedCompleteness.localRegroup,
  GUT.DuqlOrderedCompleteness.localRepresentation => Physics.DuqlOrderedCompleteness.localRepresentation,
  GUT.DuqlOrderedCompleteness.localWitness => Physics.DuqlOrderedCompleteness.localWitness,
  GUT.DuqlOrderedCompleteness.localWitness.eq_1 => Physics.DuqlOrderedCompleteness.localWitness.eq_1,
  GUT.DuqlOrderedCompleteness.local_normalized => Physics.DuqlOrderedCompleteness.local_normalized,
  GUT.DuqlOrderedCompleteness.local_unique => Physics.DuqlOrderedCompleteness.local_unique,
  GUT.DuqlOrderedCompleteness.quarkSpin => Physics.DuqlOrderedCompleteness.quarkSpin,
  GUT.DuqlOrderedCompleteness.regroup => Physics.DuqlOrderedCompleteness.regroup,
  GUT.DuqlOrderedCompleteness.spin => Physics.DuqlOrderedCompleteness.spin,
  GUT.DuqlOrderedCompleteness.spinContraction => Physics.DuqlOrderedCompleteness.spinContraction,
  GUT.DuqlOrderedCompleteness.spinContraction.eq_1 => Physics.DuqlOrderedCompleteness.spinContraction.eq_1,
  GUT.DuqlOrderedCompleteness.spinSwap => Physics.DuqlOrderedCompleteness.spinSwap,
  GUT.DuqlOrderedCompleteness.spinSwap.eq_1 => Physics.DuqlOrderedCompleteness.spinSwap.eq_1,
  GUT.DuqlOrderedCompleteness.spinWitness => Physics.DuqlOrderedCompleteness.spinWitness,
  GUT.DuqlOrderedCompleteness.spinWitness.eq_1 => Physics.DuqlOrderedCompleteness.spinWitness.eq_1,
  GUT.DuqlOrderedCompleteness.spin_unique => Physics.DuqlOrderedCompleteness.spin_unique,
  GUT.DuqlOrderedCompleteness.upSpin => Physics.DuqlOrderedCompleteness.upSpin,
  GUT.StandardSMGaugeTensor.duqlIntertwiner.eq_1 => Physics.StandardSMGaugeTensor.duqlIntertwiner.eq_1,
  GUT.WeylSpinor.epsilonRight.eq_1 => Physics.WeylSpinor.epsilonRight.eq_1,
  GUT.WeylSpinor.four.eq_1 => Physics.WeylSpinor.four.eq_1
]

assert_compatible GUT.DuqlOrderedCompleteness.Coefficient => Physics.DuqlOrderedCompleteness.Coefficient
assert_compatible GUT.DuqlOrderedCompleteness.Residual => Physics.DuqlOrderedCompleteness.Residual
assert_compatible GUT.DuqlOrderedCompleteness.downSpin => Physics.DuqlOrderedCompleteness.downSpin
assert_compatible GUT.DuqlOrderedCompleteness.exists_nonzero_iff => Physics.DuqlOrderedCompleteness.exists_nonzero_iff
assert_compatible GUT.DuqlOrderedCompleteness.fields => Physics.DuqlOrderedCompleteness.fields
assert_compatible GUT.DuqlOrderedCompleteness.flavor => Physics.DuqlOrderedCompleteness.flavor
assert_compatible GUT.DuqlOrderedCompleteness.homEquiv => Physics.DuqlOrderedCompleteness.homEquiv
assert_compatible GUT.DuqlOrderedCompleteness.leptonSpin => Physics.DuqlOrderedCompleteness.leptonSpin
assert_compatible GUT.DuqlOrderedCompleteness.localContraction => Physics.DuqlOrderedCompleteness.localContraction
assert_compatible GUT.DuqlOrderedCompleteness.localContraction.eq_1 => Physics.DuqlOrderedCompleteness.localContraction.eq_1
assert_compatible GUT.DuqlOrderedCompleteness.localRegroup => Physics.DuqlOrderedCompleteness.localRegroup
assert_compatible GUT.DuqlOrderedCompleteness.localRepresentation => Physics.DuqlOrderedCompleteness.localRepresentation
assert_compatible GUT.DuqlOrderedCompleteness.localWitness => Physics.DuqlOrderedCompleteness.localWitness
assert_compatible GUT.DuqlOrderedCompleteness.localWitness.eq_1 => Physics.DuqlOrderedCompleteness.localWitness.eq_1
assert_compatible GUT.DuqlOrderedCompleteness.local_normalized => Physics.DuqlOrderedCompleteness.local_normalized
assert_compatible GUT.DuqlOrderedCompleteness.local_unique => Physics.DuqlOrderedCompleteness.local_unique
assert_compatible GUT.DuqlOrderedCompleteness.quarkSpin => Physics.DuqlOrderedCompleteness.quarkSpin
assert_compatible GUT.DuqlOrderedCompleteness.regroup => Physics.DuqlOrderedCompleteness.regroup
assert_compatible GUT.DuqlOrderedCompleteness.spin => Physics.DuqlOrderedCompleteness.spin
assert_compatible GUT.DuqlOrderedCompleteness.spinContraction => Physics.DuqlOrderedCompleteness.spinContraction
assert_compatible GUT.DuqlOrderedCompleteness.spinContraction.eq_1 => Physics.DuqlOrderedCompleteness.spinContraction.eq_1
assert_compatible GUT.DuqlOrderedCompleteness.spinSwap => Physics.DuqlOrderedCompleteness.spinSwap
assert_compatible GUT.DuqlOrderedCompleteness.spinSwap.eq_1 => Physics.DuqlOrderedCompleteness.spinSwap.eq_1
assert_compatible GUT.DuqlOrderedCompleteness.spinWitness => Physics.DuqlOrderedCompleteness.spinWitness
assert_compatible GUT.DuqlOrderedCompleteness.spinWitness.eq_1 => Physics.DuqlOrderedCompleteness.spinWitness.eq_1
assert_compatible GUT.DuqlOrderedCompleteness.spin_unique => Physics.DuqlOrderedCompleteness.spin_unique
assert_compatible GUT.DuqlOrderedCompleteness.upSpin => Physics.DuqlOrderedCompleteness.upSpin
assert_compatible GUT.StandardSMGaugeTensor.duqlIntertwiner.eq_1 => Physics.StandardSMGaugeTensor.duqlIntertwiner.eq_1
assert_compatible GUT.WeylSpinor.epsilonRight.eq_1 => Physics.WeylSpinor.epsilonRight.eq_1
assert_compatible GUT.WeylSpinor.four.eq_1 => Physics.WeylSpinor.four.eq_1
