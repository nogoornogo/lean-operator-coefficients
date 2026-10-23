import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourCompleteness
import Physics.FieldTheory.Jets.ScalarQuarticFourUpper
import Physics.FieldTheory.Jets.ScalarQuarticFourWaves
import Physics.FieldTheory.Jets.LorentzRankFour.Invariant
import Math.Algebra.ScalarFourWaveCubature
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourCompleteness.alpha => Physics.ScalarQuarticFourCompleteness.alpha,
  GUT.ScalarQuarticFourCompleteness.alpha.eq_1 => Physics.ScalarQuarticFourCompleteness.alpha.eq_1,
  GUT.ScalarQuarticFourCompleteness.annihilates => Physics.ScalarQuarticFourCompleteness.annihilates,
  GUT.ScalarQuarticFourCompleteness.arbitrary_value => Physics.ScalarQuarticFourCompleteness.arbitrary_value,
  GUT.ScalarQuarticFourCompleteness.basis_formula => Physics.ScalarQuarticFourCompleteness.basis_formula,
  GUT.ScalarQuarticFourCompleteness.basis_value => Physics.ScalarQuarticFourCompleteness.basis_value,
  GUT.ScalarQuarticFourCompleteness.beta => Physics.ScalarQuarticFourCompleteness.beta,
  GUT.ScalarQuarticFourCompleteness.beta.eq_1 => Physics.ScalarQuarticFourCompleteness.beta.eq_1,
  GUT.ScalarQuarticFourCompleteness.cast_metric => Physics.ScalarQuarticFourCompleteness.cast_metric,
  GUT.ScalarQuarticFourCompleteness.coefficient_dimension => Physics.ScalarQuarticFourCompleteness.coefficient_dimension,
  GUT.ScalarQuarticFourCompleteness.conservation => Physics.ScalarQuarticFourCompleteness.conservation,
  GUT.ScalarQuarticFourCompleteness.equivalence => Physics.ScalarQuarticFourCompleteness.equivalence,
  GUT.ScalarQuarticFourCompleteness.extraction => Physics.ScalarQuarticFourCompleteness.extraction,
  GUT.ScalarQuarticFourCompleteness.functional => Physics.ScalarQuarticFourCompleteness.functional,
  GUT.ScalarQuarticFourCompleteness.invariant => Physics.ScalarQuarticFourCompleteness.invariant,
  GUT.ScalarQuarticFourCompleteness.invariant_word => Physics.ScalarQuarticFourCompleteness.invariant_word,
  GUT.ScalarQuarticFourCompleteness.momenta => Physics.ScalarQuarticFourCompleteness.momenta,
  GUT.ScalarQuarticFourCompleteness.momenta.eq_1 => Physics.ScalarQuarticFourCompleteness.momenta.eq_1,
  GUT.ScalarQuarticFourCompleteness.normalization => Physics.ScalarQuarticFourCompleteness.normalization,
  GUT.ScalarQuarticFourCompleteness.normalized => Physics.ScalarQuarticFourCompleteness.normalized,
  GUT.ScalarQuarticFourCompleteness.normalized_nonzero => Physics.ScalarQuarticFourCompleteness.normalized_nonzero,
  GUT.ScalarQuarticFourCompleteness.normalized_value => Physics.ScalarQuarticFourCompleteness.normalized_value,
  GUT.ScalarQuarticFourCompleteness.null => Physics.ScalarQuarticFourCompleteness.null,
  GUT.ScalarQuarticFourCompleteness.reconstruction => Physics.ScalarQuarticFourCompleteness.reconstruction
]

assert_compatible GUT.ScalarQuarticFourCompleteness.alpha => Physics.ScalarQuarticFourCompleteness.alpha
assert_compatible GUT.ScalarQuarticFourCompleteness.alpha.eq_1 => Physics.ScalarQuarticFourCompleteness.alpha.eq_1
assert_compatible GUT.ScalarQuarticFourCompleteness.annihilates => Physics.ScalarQuarticFourCompleteness.annihilates
assert_compatible GUT.ScalarQuarticFourCompleteness.arbitrary_value => Physics.ScalarQuarticFourCompleteness.arbitrary_value
assert_compatible GUT.ScalarQuarticFourCompleteness.basis_formula => Physics.ScalarQuarticFourCompleteness.basis_formula
assert_compatible GUT.ScalarQuarticFourCompleteness.basis_value => Physics.ScalarQuarticFourCompleteness.basis_value
assert_compatible GUT.ScalarQuarticFourCompleteness.beta => Physics.ScalarQuarticFourCompleteness.beta
assert_compatible GUT.ScalarQuarticFourCompleteness.beta.eq_1 => Physics.ScalarQuarticFourCompleteness.beta.eq_1
assert_compatible GUT.ScalarQuarticFourCompleteness.cast_metric => Physics.ScalarQuarticFourCompleteness.cast_metric
assert_compatible GUT.ScalarQuarticFourCompleteness.coefficient_dimension => Physics.ScalarQuarticFourCompleteness.coefficient_dimension
assert_compatible GUT.ScalarQuarticFourCompleteness.conservation => Physics.ScalarQuarticFourCompleteness.conservation
assert_compatible GUT.ScalarQuarticFourCompleteness.equivalence => Physics.ScalarQuarticFourCompleteness.equivalence
assert_compatible GUT.ScalarQuarticFourCompleteness.extraction => Physics.ScalarQuarticFourCompleteness.extraction
assert_compatible GUT.ScalarQuarticFourCompleteness.functional => Physics.ScalarQuarticFourCompleteness.functional
assert_compatible GUT.ScalarQuarticFourCompleteness.invariant => Physics.ScalarQuarticFourCompleteness.invariant
assert_compatible GUT.ScalarQuarticFourCompleteness.invariant_word => Physics.ScalarQuarticFourCompleteness.invariant_word
assert_compatible GUT.ScalarQuarticFourCompleteness.momenta => Physics.ScalarQuarticFourCompleteness.momenta
assert_compatible GUT.ScalarQuarticFourCompleteness.momenta.eq_1 => Physics.ScalarQuarticFourCompleteness.momenta.eq_1
assert_compatible GUT.ScalarQuarticFourCompleteness.normalization => Physics.ScalarQuarticFourCompleteness.normalization
assert_compatible GUT.ScalarQuarticFourCompleteness.normalized => Physics.ScalarQuarticFourCompleteness.normalized
assert_compatible GUT.ScalarQuarticFourCompleteness.normalized_nonzero => Physics.ScalarQuarticFourCompleteness.normalized_nonzero
assert_compatible GUT.ScalarQuarticFourCompleteness.normalized_value => Physics.ScalarQuarticFourCompleteness.normalized_value
assert_compatible GUT.ScalarQuarticFourCompleteness.null => Physics.ScalarQuarticFourCompleteness.null
assert_compatible GUT.ScalarQuarticFourCompleteness.reconstruction => Physics.ScalarQuarticFourCompleteness.reconstruction
