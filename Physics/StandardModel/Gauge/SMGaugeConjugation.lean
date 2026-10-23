import Physics.StandardModel.Gauge.Tensors.SMGaugeConjugation
import Physics.StandardModel.Gauge.HyperchargeTensorTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.SMGaugeConjugation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGaugeConjugation.chargedDual => Physics.SMGaugeConjugation.chargedDual,
  GUT.SMGaugeConjugation.colorDual => Physics.SMGaugeConjugation.colorDual,
  GUT.SMGaugeConjugation.conjugate => Physics.SMGaugeConjugation.conjugate,
  GUT.SMGaugeConjugation.conjugate_involutive => Physics.SMGaugeConjugation.conjugate_involutive,
  GUT.SMGaugeConjugation.conjugate_surjective => Physics.SMGaugeConjugation.conjugate_surjective,
  GUT.SMGaugeConjugation.downDual => Physics.SMGaugeConjugation.downDual,
  GUT.SMGaugeConjugation.electronDual => Physics.SMGaugeConjugation.electronDual,
  GUT.SMGaugeConjugation.higgsDual => Physics.SMGaugeConjugation.higgsDual,
  GUT.SMGaugeConjugation.leptonDual => Physics.SMGaugeConjugation.leptonDual,
  GUT.SMGaugeConjugation.lineDual => Physics.SMGaugeConjugation.lineDual,
  GUT.SMGaugeConjugation.phase_conjugate => Physics.SMGaugeConjugation.phase_conjugate,
  GUT.SMGaugeConjugation.quarkDual => Physics.SMGaugeConjugation.quarkDual,
  GUT.SMGaugeConjugation.tensorConjugate => Physics.SMGaugeConjugation.tensorConjugate,
  GUT.SMGaugeConjugation.tensorDual => Physics.SMGaugeConjugation.tensorDual,
  GUT.SMGaugeConjugation.unconjugate => Physics.SMGaugeConjugation.unconjugate,
  GUT.SMGaugeConjugation.upDual => Physics.SMGaugeConjugation.upDual,
  GUT.SMGaugeConjugation.weakDual => Physics.SMGaugeConjugation.weakDual
]

assert_compatible GUT.SMGaugeConjugation.chargedDual => Physics.SMGaugeConjugation.chargedDual
assert_compatible GUT.SMGaugeConjugation.colorDual => Physics.SMGaugeConjugation.colorDual
assert_compatible GUT.SMGaugeConjugation.conjugate => Physics.SMGaugeConjugation.conjugate
assert_compatible GUT.SMGaugeConjugation.conjugate_involutive => Physics.SMGaugeConjugation.conjugate_involutive
assert_compatible GUT.SMGaugeConjugation.conjugate_surjective => Physics.SMGaugeConjugation.conjugate_surjective
assert_compatible GUT.SMGaugeConjugation.downDual => Physics.SMGaugeConjugation.downDual
assert_compatible GUT.SMGaugeConjugation.electronDual => Physics.SMGaugeConjugation.electronDual
assert_compatible GUT.SMGaugeConjugation.higgsDual => Physics.SMGaugeConjugation.higgsDual
assert_compatible GUT.SMGaugeConjugation.leptonDual => Physics.SMGaugeConjugation.leptonDual
assert_compatible GUT.SMGaugeConjugation.lineDual => Physics.SMGaugeConjugation.lineDual
assert_compatible GUT.SMGaugeConjugation.phase_conjugate => Physics.SMGaugeConjugation.phase_conjugate
assert_compatible GUT.SMGaugeConjugation.quarkDual => Physics.SMGaugeConjugation.quarkDual
assert_compatible GUT.SMGaugeConjugation.tensorConjugate => Physics.SMGaugeConjugation.tensorConjugate
assert_compatible GUT.SMGaugeConjugation.tensorDual => Physics.SMGaugeConjugation.tensorDual
assert_compatible GUT.SMGaugeConjugation.unconjugate => Physics.SMGaugeConjugation.unconjugate
assert_compatible GUT.SMGaugeConjugation.upDual => Physics.SMGaugeConjugation.upDual
assert_compatible GUT.SMGaugeConjugation.weakDual => Physics.SMGaugeConjugation.weakDual
