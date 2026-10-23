import Physics.StandardModel.Spectrum.Representations.MonitoredSMWeights
import Physics.StandardModel.Spectrum.ExactSMWeightMultiplicity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.MonitoredSMWeights instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MonitoredSMWeights.color_vector => Physics.MonitoredSMWeights.color_vector,
  GUT.MonitoredSMWeights.electron_fourteen => Physics.MonitoredSMWeights.electron_fourteen,
  GUT.MonitoredSMWeights.electron_vector_nonzero => Physics.MonitoredSMWeights.electron_vector_nonzero,
  GUT.MonitoredSMWeights.quark_three => Physics.MonitoredSMWeights.quark_three,
  GUT.MonitoredSMWeights.quark_vector_nonzero => Physics.MonitoredSMWeights.quark_vector_nonzero,
  GUT.MonitoredSMWeights.quark_zero => Physics.MonitoredSMWeights.quark_zero,
  GUT.MonitoredSMWeights.up_eight => Physics.MonitoredSMWeights.up_eight,
  GUT.MonitoredSMWeights.up_vector_nonzero => Physics.MonitoredSMWeights.up_vector_nonzero,
  GUT.MonitoredSMWeights.weak_vector => Physics.MonitoredSMWeights.weak_vector
]

assert_compatible GUT.MonitoredSMWeights.color_vector => Physics.MonitoredSMWeights.color_vector
assert_compatible GUT.MonitoredSMWeights.electron_fourteen => Physics.MonitoredSMWeights.electron_fourteen
assert_compatible GUT.MonitoredSMWeights.electron_vector_nonzero => Physics.MonitoredSMWeights.electron_vector_nonzero
assert_compatible GUT.MonitoredSMWeights.quark_three => Physics.MonitoredSMWeights.quark_three
assert_compatible GUT.MonitoredSMWeights.quark_vector_nonzero => Physics.MonitoredSMWeights.quark_vector_nonzero
assert_compatible GUT.MonitoredSMWeights.quark_zero => Physics.MonitoredSMWeights.quark_zero
assert_compatible GUT.MonitoredSMWeights.up_eight => Physics.MonitoredSMWeights.up_eight
assert_compatible GUT.MonitoredSMWeights.up_vector_nonzero => Physics.MonitoredSMWeights.up_vector_nonzero
assert_compatible GUT.MonitoredSMWeights.weak_vector => Physics.MonitoredSMWeights.weak_vector
