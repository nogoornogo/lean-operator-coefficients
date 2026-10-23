import Physics.FieldTheory.Jets.Gauge.MaxwellProbes
import Physics.FieldTheory.Jets.MaxwellLinearEquation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.MaxwellProbes instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianFieldStrength.amplitude => Physics.AbelianFieldStrength.amplitude,
  GUT.AbelianFieldStrength.amplitude.eq_1 => Physics.AbelianFieldStrength.amplitude.eq_1,
  GUT.AbelianFieldStrength.charge => Physics.AbelianFieldStrength.charge,
  GUT.AbelianFieldStrength.charge.eq_1 => Physics.AbelianFieldStrength.charge.eq_1,
  GUT.AbelianFieldStrength.dot => Physics.AbelianFieldStrength.dot,
  GUT.AbelianFieldStrength.dot.eq_1 => Physics.AbelianFieldStrength.dot.eq_1,
  GUT.AbelianFieldStrength.higher_jet_survives => Physics.AbelianFieldStrength.higher_jet_survives,
  GUT.AbelianFieldStrength.momentum => Physics.AbelianFieldStrength.momentum,
  GUT.AbelianFieldStrength.momentum.eq_1 => Physics.AbelianFieldStrength.momentum.eq_1,
  GUT.AbelianFieldStrength.onShellProbe => Physics.AbelianFieldStrength.onShellProbe,
  GUT.AbelianFieldStrength.onShellProbe_transverseJet => Physics.AbelianFieldStrength.onShellProbe_transverseJet,
  GUT.AbelianFieldStrength.probe => Physics.AbelianFieldStrength.probe,
  GUT.AbelianFieldStrength.probe.eq_1 => Physics.AbelianFieldStrength.probe.eq_1,
  GUT.AbelianFieldStrength.probe_annihilates => Physics.AbelianFieldStrength.probe_annihilates,
  GUT.AbelianFieldStrength.probe_antisymmetry => Physics.AbelianFieldStrength.probe_antisymmetry,
  GUT.AbelianFieldStrength.probe_bianchi => Physics.AbelianFieldStrength.probe_bianchi,
  GUT.AbelianFieldStrength.probe_directional => Physics.AbelianFieldStrength.probe_directional,
  GUT.AbelianFieldStrength.probe_maxwell => Physics.AbelianFieldStrength.probe_maxwell,
  GUT.AbelianFieldStrength.probe_multiple => Physics.AbelianFieldStrength.probe_multiple,
  GUT.AbelianFieldStrength.probe_ofSymbols => Physics.AbelianFieldStrength.probe_ofSymbols,
  GUT.AbelianFieldStrength.probe_seed => Physics.AbelianFieldStrength.probe_seed,
  GUT.AbelianFieldStrength.probe_shift => Physics.AbelianFieldStrength.probe_shift,
  GUT.AbelianFieldStrength.probe_zeroPair => Physics.AbelianFieldStrength.probe_zeroPair,
  GUT.AbelianFieldStrength.raised => Physics.AbelianFieldStrength.raised,
  GUT.AbelianFieldStrength.raised.eq_1 => Physics.AbelianFieldStrength.raised.eq_1,
  GUT.AbelianFieldStrength.symmetric_higher_jet_survives => Physics.AbelianFieldStrength.symmetric_higher_jet_survives,
  GUT.AbelianFieldStrength.transverseDirection => Physics.AbelianFieldStrength.transverseDirection,
  GUT.AbelianFieldStrength.transverseDirection.eq_1 => Physics.AbelianFieldStrength.transverseDirection.eq_1,
  GUT.AbelianFieldStrength.transverseJet => Physics.AbelianFieldStrength.transverseJet,
  GUT.AbelianFieldStrength.transverse_independent => Physics.AbelianFieldStrength.transverse_independent
]

assert_compatible GUT.AbelianFieldStrength.amplitude => Physics.AbelianFieldStrength.amplitude
assert_compatible GUT.AbelianFieldStrength.amplitude.eq_1 => Physics.AbelianFieldStrength.amplitude.eq_1
assert_compatible GUT.AbelianFieldStrength.charge => Physics.AbelianFieldStrength.charge
assert_compatible GUT.AbelianFieldStrength.charge.eq_1 => Physics.AbelianFieldStrength.charge.eq_1
assert_compatible GUT.AbelianFieldStrength.dot => Physics.AbelianFieldStrength.dot
assert_compatible GUT.AbelianFieldStrength.dot.eq_1 => Physics.AbelianFieldStrength.dot.eq_1
assert_compatible GUT.AbelianFieldStrength.higher_jet_survives => Physics.AbelianFieldStrength.higher_jet_survives
assert_compatible GUT.AbelianFieldStrength.momentum => Physics.AbelianFieldStrength.momentum
assert_compatible GUT.AbelianFieldStrength.momentum.eq_1 => Physics.AbelianFieldStrength.momentum.eq_1
assert_compatible GUT.AbelianFieldStrength.onShellProbe => Physics.AbelianFieldStrength.onShellProbe
assert_compatible GUT.AbelianFieldStrength.onShellProbe_transverseJet => Physics.AbelianFieldStrength.onShellProbe_transverseJet
assert_compatible GUT.AbelianFieldStrength.probe => Physics.AbelianFieldStrength.probe
assert_compatible GUT.AbelianFieldStrength.probe.eq_1 => Physics.AbelianFieldStrength.probe.eq_1
assert_compatible GUT.AbelianFieldStrength.probe_annihilates => Physics.AbelianFieldStrength.probe_annihilates
assert_compatible GUT.AbelianFieldStrength.probe_antisymmetry => Physics.AbelianFieldStrength.probe_antisymmetry
assert_compatible GUT.AbelianFieldStrength.probe_bianchi => Physics.AbelianFieldStrength.probe_bianchi
assert_compatible GUT.AbelianFieldStrength.probe_directional => Physics.AbelianFieldStrength.probe_directional
assert_compatible GUT.AbelianFieldStrength.probe_maxwell => Physics.AbelianFieldStrength.probe_maxwell
assert_compatible GUT.AbelianFieldStrength.probe_multiple => Physics.AbelianFieldStrength.probe_multiple
assert_compatible GUT.AbelianFieldStrength.probe_ofSymbols => Physics.AbelianFieldStrength.probe_ofSymbols
assert_compatible GUT.AbelianFieldStrength.probe_seed => Physics.AbelianFieldStrength.probe_seed
assert_compatible GUT.AbelianFieldStrength.probe_shift => Physics.AbelianFieldStrength.probe_shift
assert_compatible GUT.AbelianFieldStrength.probe_zeroPair => Physics.AbelianFieldStrength.probe_zeroPair
assert_compatible GUT.AbelianFieldStrength.raised => Physics.AbelianFieldStrength.raised
assert_compatible GUT.AbelianFieldStrength.raised.eq_1 => Physics.AbelianFieldStrength.raised.eq_1
assert_compatible GUT.AbelianFieldStrength.symmetric_higher_jet_survives => Physics.AbelianFieldStrength.symmetric_higher_jet_survives
assert_compatible GUT.AbelianFieldStrength.transverseDirection => Physics.AbelianFieldStrength.transverseDirection
assert_compatible GUT.AbelianFieldStrength.transverseDirection.eq_1 => Physics.AbelianFieldStrength.transverseDirection.eq_1
assert_compatible GUT.AbelianFieldStrength.transverseJet => Physics.AbelianFieldStrength.transverseJet
assert_compatible GUT.AbelianFieldStrength.transverse_independent => Physics.AbelianFieldStrength.transverse_independent
