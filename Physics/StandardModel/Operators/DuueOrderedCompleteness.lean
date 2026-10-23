import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueOrderedCompleteness
import Physics.StandardModel.Gauge.DuueGaugeUniqueness
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueOrderedCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuueOrderedCompleteness.Coefficient => Physics.DuueOrderedCompleteness.Coefficient,
  GUT.DuueOrderedCompleteness.Residual => Physics.DuueOrderedCompleteness.Residual,
  GUT.DuueOrderedCompleteness.assemble_apply => Physics.DuueOrderedCompleteness.assemble_apply,
  GUT.DuueOrderedCompleteness.downSpin => Physics.DuueOrderedCompleteness.downSpin,
  GUT.DuueOrderedCompleteness.electronSpin => Physics.DuueOrderedCompleteness.electronSpin,
  GUT.DuueOrderedCompleteness.fields => Physics.DuueOrderedCompleteness.fields,
  GUT.DuueOrderedCompleteness.flavor => Physics.DuueOrderedCompleteness.flavor,
  GUT.DuueOrderedCompleteness.homEquiv => Physics.DuueOrderedCompleteness.homEquiv,
  GUT.DuueOrderedCompleteness.localPairing => Physics.DuueOrderedCompleteness.localPairing,
  GUT.DuueOrderedCompleteness.localPairing.eq_1 => Physics.DuueOrderedCompleteness.localPairing.eq_1,
  GUT.DuueOrderedCompleteness.localPairing_probe => Physics.DuueOrderedCompleteness.localPairing_probe,
  GUT.DuueOrderedCompleteness.localProbe => Physics.DuueOrderedCompleteness.localProbe,
  GUT.DuueOrderedCompleteness.localRegroup => Physics.DuueOrderedCompleteness.localRegroup,
  GUT.DuueOrderedCompleteness.localRepresentation => Physics.DuueOrderedCompleteness.localRepresentation,
  GUT.DuueOrderedCompleteness.local_formula => Physics.DuueOrderedCompleteness.local_formula,
  GUT.DuueOrderedCompleteness.regroup => Physics.DuueOrderedCompleteness.regroup,
  GUT.DuueOrderedCompleteness.upSpin => Physics.DuueOrderedCompleteness.upSpin
]

assert_compatible GUT.DuueOrderedCompleteness.Coefficient => Physics.DuueOrderedCompleteness.Coefficient
assert_compatible GUT.DuueOrderedCompleteness.Residual => Physics.DuueOrderedCompleteness.Residual
assert_compatible GUT.DuueOrderedCompleteness.assemble_apply => Physics.DuueOrderedCompleteness.assemble_apply
assert_compatible GUT.DuueOrderedCompleteness.downSpin => Physics.DuueOrderedCompleteness.downSpin
assert_compatible GUT.DuueOrderedCompleteness.electronSpin => Physics.DuueOrderedCompleteness.electronSpin
assert_compatible GUT.DuueOrderedCompleteness.fields => Physics.DuueOrderedCompleteness.fields
assert_compatible GUT.DuueOrderedCompleteness.flavor => Physics.DuueOrderedCompleteness.flavor
assert_compatible GUT.DuueOrderedCompleteness.homEquiv => Physics.DuueOrderedCompleteness.homEquiv
assert_compatible GUT.DuueOrderedCompleteness.localPairing => Physics.DuueOrderedCompleteness.localPairing
assert_compatible GUT.DuueOrderedCompleteness.localPairing.eq_1 => Physics.DuueOrderedCompleteness.localPairing.eq_1
assert_compatible GUT.DuueOrderedCompleteness.localPairing_probe => Physics.DuueOrderedCompleteness.localPairing_probe
assert_compatible GUT.DuueOrderedCompleteness.localProbe => Physics.DuueOrderedCompleteness.localProbe
assert_compatible GUT.DuueOrderedCompleteness.localRegroup => Physics.DuueOrderedCompleteness.localRegroup
assert_compatible GUT.DuueOrderedCompleteness.localRepresentation => Physics.DuueOrderedCompleteness.localRepresentation
assert_compatible GUT.DuueOrderedCompleteness.local_formula => Physics.DuueOrderedCompleteness.local_formula
assert_compatible GUT.DuueOrderedCompleteness.regroup => Physics.DuueOrderedCompleteness.regroup
assert_compatible GUT.DuueOrderedCompleteness.upSpin => Physics.DuueOrderedCompleteness.upSpin
