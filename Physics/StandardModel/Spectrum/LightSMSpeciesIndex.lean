import Physics.StandardModel.Spectrum.Mass.LightSMSpeciesIndex
import Physics.StandardModel.Gauge.LightSMAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Mass.LightSMSpeciesIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightSMSpeciesIndex.HasTarget => Physics.LightSMSpeciesIndex.HasTarget,
  GUT.LightSMSpeciesIndex.common_quotient => Physics.LightSMSpeciesIndex.common_quotient,
  GUT.LightSMSpeciesIndex.electron => Physics.LightSMSpeciesIndex.electron,
  GUT.LightSMSpeciesIndex.quark => Physics.LightSMSpeciesIndex.quark,
  GUT.LightSMSpeciesIndex.up => Physics.LightSMSpeciesIndex.up
]

assert_compatible GUT.LightSMSpeciesIndex.HasTarget => Physics.LightSMSpeciesIndex.HasTarget
assert_compatible GUT.LightSMSpeciesIndex.common_quotient => Physics.LightSMSpeciesIndex.common_quotient
assert_compatible GUT.LightSMSpeciesIndex.electron => Physics.LightSMSpeciesIndex.electron
assert_compatible GUT.LightSMSpeciesIndex.quark => Physics.LightSMSpeciesIndex.quark
assert_compatible GUT.LightSMSpeciesIndex.up => Physics.LightSMSpeciesIndex.up
