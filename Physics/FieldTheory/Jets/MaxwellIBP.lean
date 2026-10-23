import Physics.FieldTheory.Jets.Gauge.MaxwellIBP
import Physics.FieldTheory.Jets.MaxwellWave
import Physics.FieldTheory.Jets.MaxwellProbes
import Math.Algebra.LinearJetKernel
import Math.RepresentationTheory.LinearJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.MaxwellIBP instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianFieldStrength.Algebra => Physics.AbelianFieldStrength.Algebra,
  GUT.AbelianFieldStrength.algebraAction => Physics.AbelianFieldStrength.algebraAction,
  GUT.AbelianFieldStrength.algebraProbe => Physics.AbelianFieldStrength.algebraProbe,
  GUT.AbelianFieldStrength.algebraProbe_evenJet => Physics.AbelianFieldStrength.algebraProbe_evenJet,
  GUT.AbelianFieldStrength.coefficientEquiv => Physics.AbelianFieldStrength.coefficientEquiv,
  GUT.AbelianFieldStrength.equation_descendant_zero => Physics.AbelianFieldStrength.equation_descendant_zero,
  GUT.AbelianFieldStrength.evenEquiv => Physics.AbelianFieldStrength.evenEquiv,
  GUT.AbelianFieldStrength.evenEquiv.eq_1 => Physics.AbelianFieldStrength.evenEquiv.eq_1,
  GUT.AbelianFieldStrength.evenEquiv_evenJet => Physics.AbelianFieldStrength.evenEquiv_evenJet,
  GUT.AbelianFieldStrength.evenJet => Physics.AbelianFieldStrength.evenJet,
  GUT.AbelianFieldStrength.evenJet.eq_1 => Physics.AbelianFieldStrength.evenJet.eq_1,
  GUT.AbelianFieldStrength.evenJet_nonzero => Physics.AbelianFieldStrength.evenJet_nonzero,
  GUT.AbelianFieldStrength.finite_source => Physics.AbelianFieldStrength.finite_source,
  GUT.AbelianFieldStrength.higher_even_jet_survives => Physics.AbelianFieldStrength.higher_even_jet_survives,
  GUT.AbelianFieldStrength.kernel_presentation => Physics.AbelianFieldStrength.kernel_presentation,
  GUT.AbelianFieldStrength.oddEquations => Physics.AbelianFieldStrength.oddEquations,
  GUT.AbelianFieldStrength.oddField => Physics.AbelianFieldStrength.oddField,
  GUT.AbelianFieldStrength.oddSeed => Physics.AbelianFieldStrength.oddSeed,
  GUT.AbelianFieldStrength.oddSeed.eq_1 => Physics.AbelianFieldStrength.oddSeed.eq_1,
  GUT.AbelianFieldStrength.odd_covariant => Physics.AbelianFieldStrength.odd_covariant,
  GUT.AbelianFieldStrength.projection => Physics.AbelianFieldStrength.projection,
  GUT.AbelianFieldStrength.projection_derivative => Physics.AbelianFieldStrength.projection_derivative,
  GUT.AbelianFieldStrength.projection_evenJet => Physics.AbelianFieldStrength.projection_evenJet,
  GUT.AbelianFieldStrength.projection_surjective => Physics.AbelianFieldStrength.projection_surjective,
  GUT.AbelianFieldStrength.sourceEquiv => Physics.AbelianFieldStrength.sourceEquiv
]

assert_compatible GUT.AbelianFieldStrength.Algebra => Physics.AbelianFieldStrength.Algebra
assert_compatible GUT.AbelianFieldStrength.algebraAction => Physics.AbelianFieldStrength.algebraAction
assert_compatible GUT.AbelianFieldStrength.algebraProbe => Physics.AbelianFieldStrength.algebraProbe
assert_compatible GUT.AbelianFieldStrength.algebraProbe_evenJet => Physics.AbelianFieldStrength.algebraProbe_evenJet
assert_compatible GUT.AbelianFieldStrength.coefficientEquiv => Physics.AbelianFieldStrength.coefficientEquiv
assert_compatible GUT.AbelianFieldStrength.equation_descendant_zero => Physics.AbelianFieldStrength.equation_descendant_zero
assert_compatible GUT.AbelianFieldStrength.evenEquiv => Physics.AbelianFieldStrength.evenEquiv
assert_compatible GUT.AbelianFieldStrength.evenEquiv.eq_1 => Physics.AbelianFieldStrength.evenEquiv.eq_1
assert_compatible GUT.AbelianFieldStrength.evenEquiv_evenJet => Physics.AbelianFieldStrength.evenEquiv_evenJet
assert_compatible GUT.AbelianFieldStrength.evenJet => Physics.AbelianFieldStrength.evenJet
assert_compatible GUT.AbelianFieldStrength.evenJet.eq_1 => Physics.AbelianFieldStrength.evenJet.eq_1
assert_compatible GUT.AbelianFieldStrength.evenJet_nonzero => Physics.AbelianFieldStrength.evenJet_nonzero
assert_compatible GUT.AbelianFieldStrength.finite_source => Physics.AbelianFieldStrength.finite_source
assert_compatible GUT.AbelianFieldStrength.higher_even_jet_survives => Physics.AbelianFieldStrength.higher_even_jet_survives
assert_compatible GUT.AbelianFieldStrength.kernel_presentation => Physics.AbelianFieldStrength.kernel_presentation
assert_compatible GUT.AbelianFieldStrength.oddEquations => Physics.AbelianFieldStrength.oddEquations
assert_compatible GUT.AbelianFieldStrength.oddField => Physics.AbelianFieldStrength.oddField
assert_compatible GUT.AbelianFieldStrength.oddSeed => Physics.AbelianFieldStrength.oddSeed
assert_compatible GUT.AbelianFieldStrength.oddSeed.eq_1 => Physics.AbelianFieldStrength.oddSeed.eq_1
assert_compatible GUT.AbelianFieldStrength.odd_covariant => Physics.AbelianFieldStrength.odd_covariant
assert_compatible GUT.AbelianFieldStrength.projection => Physics.AbelianFieldStrength.projection
assert_compatible GUT.AbelianFieldStrength.projection_derivative => Physics.AbelianFieldStrength.projection_derivative
assert_compatible GUT.AbelianFieldStrength.projection_evenJet => Physics.AbelianFieldStrength.projection_evenJet
assert_compatible GUT.AbelianFieldStrength.projection_surjective => Physics.AbelianFieldStrength.projection_surjective
assert_compatible GUT.AbelianFieldStrength.sourceEquiv => Physics.AbelianFieldStrength.sourceEquiv
