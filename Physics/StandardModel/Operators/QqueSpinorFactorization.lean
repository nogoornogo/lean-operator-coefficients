import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorFactorization
import Physics.StandardModel.Operators.QqueSpinorExterior
import Physics.FieldTheory.Spinor.WeylSpinorUniqueness
import Math.RepresentationTheory.ExternalInvariantFactorization
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorFactorization instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueSpinorExterior.ordered.eq_1 => Physics.QqueSpinorExterior.ordered.eq_1,
  GUT.QqueSpinorFactorization.reconstruct => Physics.QqueSpinorFactorization.reconstruct,
  GUT.QqueSpinorFactorization.regrouped => Physics.QqueSpinorFactorization.regrouped,
  GUT.QqueSpinorFactorization.regrouped.eq_1 => Physics.QqueSpinorFactorization.regrouped.eq_1,
  GUT.QqueSpinorFactorization.spinorWitness => Physics.QqueSpinorFactorization.spinorWitness,
  GUT.QqueSpinorFactorization.strip => Physics.QqueSpinorFactorization.strip,
  GUT.QqueSpinorFactorization.strip.eq_1 => Physics.QqueSpinorFactorization.strip.eq_1
]

assert_compatible GUT.QqueSpinorExterior.ordered.eq_1 => Physics.QqueSpinorExterior.ordered.eq_1
assert_compatible GUT.QqueSpinorFactorization.reconstruct => Physics.QqueSpinorFactorization.reconstruct
assert_compatible GUT.QqueSpinorFactorization.regrouped => Physics.QqueSpinorFactorization.regrouped
assert_compatible GUT.QqueSpinorFactorization.regrouped.eq_1 => Physics.QqueSpinorFactorization.regrouped.eq_1
assert_compatible GUT.QqueSpinorFactorization.spinorWitness => Physics.QqueSpinorFactorization.spinorWitness
assert_compatible GUT.QqueSpinorFactorization.strip => Physics.QqueSpinorFactorization.strip
assert_compatible GUT.QqueSpinorFactorization.strip.eq_1 => Physics.QqueSpinorFactorization.strip.eq_1
