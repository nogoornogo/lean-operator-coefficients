import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentInvariance
import Physics.FieldTheory.Jets.HiggsQuarticFourMomentBasis
import Physics.FieldTheory.Jets.HiggsQuarticFourUpper
import Physics.FieldTheory.Jets.LorentzRankFour.ThreeInvariant
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentInvariance instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourMomentInvariance.Moments => Physics.HiggsQuarticFourMomentInvariance.Moments,
  GUT.HiggsQuarticFourMomentInvariance.basis_formula => Physics.HiggsQuarticFourMomentInvariance.basis_formula,
  GUT.HiggsQuarticFourMomentInvariance.cast_metric => Physics.HiggsQuarticFourMomentInvariance.cast_metric,
  GUT.HiggsQuarticFourMomentInvariance.channel => Physics.HiggsQuarticFourMomentInvariance.channel,
  GUT.HiggsQuarticFourMomentInvariance.channel.eq_1 => Physics.HiggsQuarticFourMomentInvariance.channel.eq_1,
  GUT.HiggsQuarticFourMomentInvariance.coefficient => Physics.HiggsQuarticFourMomentInvariance.coefficient,
  GUT.HiggsQuarticFourMomentInvariance.coefficient_apply => Physics.HiggsQuarticFourMomentInvariance.coefficient_apply,
  GUT.HiggsQuarticFourMomentInvariance.coordinate => Physics.HiggsQuarticFourMomentInvariance.coordinate,
  GUT.HiggsQuarticFourMomentInvariance.coordinate.eq_1 => Physics.HiggsQuarticFourMomentInvariance.coordinate.eq_1,
  GUT.HiggsQuarticFourMomentInvariance.expected_value => Physics.HiggsQuarticFourMomentInvariance.expected_value,
  GUT.HiggsQuarticFourMomentInvariance.invariant => Physics.HiggsQuarticFourMomentInvariance.invariant,
  GUT.HiggsQuarticFourMomentInvariance.lorentz => Physics.HiggsQuarticFourMomentInvariance.lorentz,
  GUT.HiggsQuarticFourMomentInvariance.lorentz_word => Physics.HiggsQuarticFourMomentInvariance.lorentz_word
]

assert_compatible GUT.HiggsQuarticFourMomentInvariance.Moments => Physics.HiggsQuarticFourMomentInvariance.Moments
assert_compatible GUT.HiggsQuarticFourMomentInvariance.basis_formula => Physics.HiggsQuarticFourMomentInvariance.basis_formula
assert_compatible GUT.HiggsQuarticFourMomentInvariance.cast_metric => Physics.HiggsQuarticFourMomentInvariance.cast_metric
assert_compatible GUT.HiggsQuarticFourMomentInvariance.channel => Physics.HiggsQuarticFourMomentInvariance.channel
assert_compatible GUT.HiggsQuarticFourMomentInvariance.channel.eq_1 => Physics.HiggsQuarticFourMomentInvariance.channel.eq_1
assert_compatible GUT.HiggsQuarticFourMomentInvariance.coefficient => Physics.HiggsQuarticFourMomentInvariance.coefficient
assert_compatible GUT.HiggsQuarticFourMomentInvariance.coefficient_apply => Physics.HiggsQuarticFourMomentInvariance.coefficient_apply
assert_compatible GUT.HiggsQuarticFourMomentInvariance.coordinate => Physics.HiggsQuarticFourMomentInvariance.coordinate
assert_compatible GUT.HiggsQuarticFourMomentInvariance.coordinate.eq_1 => Physics.HiggsQuarticFourMomentInvariance.coordinate.eq_1
assert_compatible GUT.HiggsQuarticFourMomentInvariance.expected_value => Physics.HiggsQuarticFourMomentInvariance.expected_value
assert_compatible GUT.HiggsQuarticFourMomentInvariance.invariant => Physics.HiggsQuarticFourMomentInvariance.invariant
assert_compatible GUT.HiggsQuarticFourMomentInvariance.lorentz => Physics.HiggsQuarticFourMomentInvariance.lorentz
assert_compatible GUT.HiggsQuarticFourMomentInvariance.lorentz_word => Physics.HiggsQuarticFourMomentInvariance.lorentz_word
