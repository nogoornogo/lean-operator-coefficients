import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCompleteness
import Physics.FieldTheory.Jets.WeylHiggsWaveInvariant
import Physics.FieldTheory.Jets.WeylHiggsUpper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsCompleteness.coefficient_dimension => Physics.WeylHiggsCompleteness.coefficient_dimension,
  GUT.WeylHiggsCompleteness.equivalence => Physics.WeylHiggsCompleteness.equivalence,
  GUT.WeylHiggsCompleteness.evaluate_reconstruction => Physics.WeylHiggsCompleteness.evaluate_reconstruction,
  GUT.WeylHiggsCompleteness.extract_reconstruction => Physics.WeylHiggsCompleteness.extract_reconstruction,
  GUT.WeylHiggsCompleteness.extraction => Physics.WeylHiggsCompleteness.extraction,
  GUT.WeylHiggsCompleteness.generatedEquivalence => Physics.WeylHiggsCompleteness.generatedEquivalence,
  GUT.WeylHiggsCompleteness.generated_dimension => Physics.WeylHiggsCompleteness.generated_dimension,
  GUT.WeylHiggsCompleteness.generated_extraction => Physics.WeylHiggsCompleteness.generated_extraction,
  GUT.WeylHiggsCompleteness.input_agreement => Physics.WeylHiggsCompleteness.input_agreement,
  GUT.WeylHiggsCompleteness.normalized => Physics.WeylHiggsCompleteness.normalized,
  GUT.WeylHiggsCompleteness.normalized.eq_1 => Physics.WeylHiggsCompleteness.normalized.eq_1,
  GUT.WeylHiggsCompleteness.normalized_nonzero => Physics.WeylHiggsCompleteness.normalized_nonzero,
  GUT.WeylHiggsCompleteness.normalized_value => Physics.WeylHiggsCompleteness.normalized_value,
  GUT.WeylHiggsCompleteness.reconstruct => Physics.WeylHiggsCompleteness.reconstruct,
  GUT.WeylHiggsCompleteness.reconstruction => Physics.WeylHiggsCompleteness.reconstruction
]

assert_compatible GUT.WeylHiggsCompleteness.coefficient_dimension => Physics.WeylHiggsCompleteness.coefficient_dimension
assert_compatible GUT.WeylHiggsCompleteness.equivalence => Physics.WeylHiggsCompleteness.equivalence
assert_compatible GUT.WeylHiggsCompleteness.evaluate_reconstruction => Physics.WeylHiggsCompleteness.evaluate_reconstruction
assert_compatible GUT.WeylHiggsCompleteness.extract_reconstruction => Physics.WeylHiggsCompleteness.extract_reconstruction
assert_compatible GUT.WeylHiggsCompleteness.extraction => Physics.WeylHiggsCompleteness.extraction
assert_compatible GUT.WeylHiggsCompleteness.generatedEquivalence => Physics.WeylHiggsCompleteness.generatedEquivalence
assert_compatible GUT.WeylHiggsCompleteness.generated_dimension => Physics.WeylHiggsCompleteness.generated_dimension
assert_compatible GUT.WeylHiggsCompleteness.generated_extraction => Physics.WeylHiggsCompleteness.generated_extraction
assert_compatible GUT.WeylHiggsCompleteness.input_agreement => Physics.WeylHiggsCompleteness.input_agreement
assert_compatible GUT.WeylHiggsCompleteness.normalized => Physics.WeylHiggsCompleteness.normalized
assert_compatible GUT.WeylHiggsCompleteness.normalized.eq_1 => Physics.WeylHiggsCompleteness.normalized.eq_1
assert_compatible GUT.WeylHiggsCompleteness.normalized_nonzero => Physics.WeylHiggsCompleteness.normalized_nonzero
assert_compatible GUT.WeylHiggsCompleteness.normalized_value => Physics.WeylHiggsCompleteness.normalized_value
assert_compatible GUT.WeylHiggsCompleteness.reconstruct => Physics.WeylHiggsCompleteness.reconstruct
assert_compatible GUT.WeylHiggsCompleteness.reconstruction => Physics.WeylHiggsCompleteness.reconstruction
