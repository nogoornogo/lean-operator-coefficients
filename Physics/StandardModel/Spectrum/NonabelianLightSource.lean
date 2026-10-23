import Physics.StandardModel.Spectrum.Mass.NonabelianLightSource
import Physics.StandardModel.Spectrum.NonabelianSMTarget
import Physics.FieldTheory.Mass.ResidualLightQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Mass.NonabelianLightSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NonabelianLightSource.common_barFive_quotient => Physics.NonabelianLightSource.common_barFive_quotient,
  GUT.NonabelianLightSource.common_ten_quotient => Physics.NonabelianLightSource.common_ten_quotient,
  GUT.NonabelianLightSource.lightSector => Physics.NonabelianLightSource.lightSector
]

assert_compatible GUT.NonabelianLightSource.common_barFive_quotient => Physics.NonabelianLightSource.common_barFive_quotient
assert_compatible GUT.NonabelianLightSource.common_ten_quotient => Physics.NonabelianLightSource.common_ten_quotient
assert_compatible GUT.NonabelianLightSource.lightSector => Physics.NonabelianLightSource.lightSector
