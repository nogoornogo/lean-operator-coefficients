import Physics.StandardModel.Spectrum.Representations.Audit.AuditExactSMSpectrum
import Physics.StandardModel.Operators.ExactSMSpectrumQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.Audit.AuditExactSMSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMSpectrumAudit.dimension => Physics.ExactSMSpectrumAudit.dimension,
  GUT.ExactSMSpectrumAudit.model_has_spectrum => Physics.ExactSMSpectrumAudit.model_has_spectrum,
  GUT.ExactSMSpectrumAudit.monitored_and_opposite => Physics.ExactSMSpectrumAudit.monitored_and_opposite,
  GUT.ExactSMSpectrumAudit.no_opposites => Physics.ExactSMSpectrumAudit.no_opposites,
  GUT.ExactSMSpectrumAudit.one_generation => Physics.ExactSMSpectrumAudit.one_generation,
  GUT.ExactSMSpectrumAudit.singlets_do_not_supply_quarks => Physics.ExactSMSpectrumAudit.singlets_do_not_supply_quarks,
  GUT.ExactSMSpectrumAudit.three_generations_with_singlets => Physics.ExactSMSpectrumAudit.three_generations_with_singlets,
  GUT.ExactSMSpectrumAudit.zero_generations => Physics.ExactSMSpectrumAudit.zero_generations
]

assert_compatible GUT.ExactSMSpectrumAudit.dimension => Physics.ExactSMSpectrumAudit.dimension
assert_compatible GUT.ExactSMSpectrumAudit.model_has_spectrum => Physics.ExactSMSpectrumAudit.model_has_spectrum
assert_compatible GUT.ExactSMSpectrumAudit.monitored_and_opposite => Physics.ExactSMSpectrumAudit.monitored_and_opposite
assert_compatible GUT.ExactSMSpectrumAudit.no_opposites => Physics.ExactSMSpectrumAudit.no_opposites
assert_compatible GUT.ExactSMSpectrumAudit.one_generation => Physics.ExactSMSpectrumAudit.one_generation
assert_compatible GUT.ExactSMSpectrumAudit.singlets_do_not_supply_quarks => Physics.ExactSMSpectrumAudit.singlets_do_not_supply_quarks
assert_compatible GUT.ExactSMSpectrumAudit.three_generations_with_singlets => Physics.ExactSMSpectrumAudit.three_generations_with_singlets
assert_compatible GUT.ExactSMSpectrumAudit.zero_generations => Physics.ExactSMSpectrumAudit.zero_generations
