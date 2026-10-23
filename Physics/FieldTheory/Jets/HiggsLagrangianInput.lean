import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsLagrangianInput
import Math.RepresentationTheory.HiggsLagrangianInput
import Physics.FieldTheory.Jets.LorentzJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.Inputs.HiggsLagrangianInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsLagrangianInput.action => Physics.HiggsLagrangianInput.action,
  GUT.HiggsLagrangianInput.covariance => Physics.HiggsLagrangianInput.covariance,
  GUT.HiggsLagrangianInput.extraction => Physics.HiggsLagrangianInput.extraction,
  GUT.HiggsLagrangianInput.field_invariant => Physics.HiggsLagrangianInput.field_invariant,
  GUT.HiggsLagrangianInput.generated_stable => Physics.HiggsLagrangianInput.generated_stable,
  GUT.HiggsLagrangianInput.ideal_stable => Physics.HiggsLagrangianInput.ideal_stable,
  GUT.HiggsLagrangianInput.input => Physics.HiggsLagrangianInput.input,
  GUT.HiggsLagrangianInput.linearSymbol => Physics.HiggsLagrangianInput.linearSymbol,
  GUT.HiggsLagrangianInput.linearSymbol.eq_1 => Physics.HiggsLagrangianInput.linearSymbol.eq_1,
  GUT.HiggsLagrangianInput.linearSymbol_natural => Physics.HiggsLagrangianInput.linearSymbol_natural,
  GUT.HiggsLagrangianInput.linearSymbol_one => Physics.HiggsLagrangianInput.linearSymbol_one,
  GUT.HiggsLagrangianInput.linearSymbol_wave => Physics.HiggsLagrangianInput.linearSymbol_wave,
  GUT.HiggsLagrangianInput.rho_invariant => Physics.HiggsLagrangianInput.rho_invariant,
  GUT.HiggsLagrangianInput.seed_invariant => Physics.HiggsLagrangianInput.seed_invariant,
  GUT.HiggsLagrangianInput.stable => Physics.HiggsLagrangianInput.stable,
  GUT.HiggsLagrangianInput.transport => Physics.HiggsLagrangianInput.transport,
  GUT.HiggsLagrangianInput.wave_invariant => Physics.HiggsLagrangianInput.wave_invariant
]

assert_compatible GUT.HiggsLagrangianInput.action => Physics.HiggsLagrangianInput.action
assert_compatible GUT.HiggsLagrangianInput.covariance => Physics.HiggsLagrangianInput.covariance
assert_compatible GUT.HiggsLagrangianInput.extraction => Physics.HiggsLagrangianInput.extraction
assert_compatible GUT.HiggsLagrangianInput.field_invariant => Physics.HiggsLagrangianInput.field_invariant
assert_compatible GUT.HiggsLagrangianInput.generated_stable => Physics.HiggsLagrangianInput.generated_stable
assert_compatible GUT.HiggsLagrangianInput.ideal_stable => Physics.HiggsLagrangianInput.ideal_stable
assert_compatible GUT.HiggsLagrangianInput.input => Physics.HiggsLagrangianInput.input
assert_compatible GUT.HiggsLagrangianInput.linearSymbol => Physics.HiggsLagrangianInput.linearSymbol
assert_compatible GUT.HiggsLagrangianInput.linearSymbol.eq_1 => Physics.HiggsLagrangianInput.linearSymbol.eq_1
assert_compatible GUT.HiggsLagrangianInput.linearSymbol_natural => Physics.HiggsLagrangianInput.linearSymbol_natural
assert_compatible GUT.HiggsLagrangianInput.linearSymbol_one => Physics.HiggsLagrangianInput.linearSymbol_one
assert_compatible GUT.HiggsLagrangianInput.linearSymbol_wave => Physics.HiggsLagrangianInput.linearSymbol_wave
assert_compatible GUT.HiggsLagrangianInput.rho_invariant => Physics.HiggsLagrangianInput.rho_invariant
assert_compatible GUT.HiggsLagrangianInput.seed_invariant => Physics.HiggsLagrangianInput.seed_invariant
assert_compatible GUT.HiggsLagrangianInput.stable => Physics.HiggsLagrangianInput.stable
assert_compatible GUT.HiggsLagrangianInput.transport => Physics.HiggsLagrangianInput.transport
assert_compatible GUT.HiggsLagrangianInput.wave_invariant => Physics.HiggsLagrangianInput.wave_invariant
