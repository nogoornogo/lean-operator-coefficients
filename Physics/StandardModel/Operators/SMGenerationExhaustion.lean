import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationExhaustion
import Math.RepresentationTheory.GenerationExteriorExhaustion
import Math.RepresentationTheory.IndexedExteriorContent
import Physics.StandardModel.Operators.SMCombinedCompactAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMGenerationExhaustion instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGenerationExhaustion.Core => Physics.SMGenerationExhaustion.Core,
  GUT.SMGenerationExhaustion.FactorCarrier => Physics.SMGenerationExhaustion.FactorCarrier,
  GUT.SMGenerationExhaustion.Fits => Physics.SMGenerationExhaustion.Fits,
  GUT.SMGenerationExhaustion.Fits.eq_1 => Physics.SMGenerationExhaustion.Fits.eq_1,
  GUT.SMGenerationExhaustion.Occupation => Physics.SMGenerationExhaustion.Occupation,
  GUT.SMGenerationExhaustion.actual_field => Physics.SMGenerationExhaustion.actual_field,
  GUT.SMGenerationExhaustion.core => Physics.SMGenerationExhaustion.core,
  GUT.SMGenerationExhaustion.coreFinite => Physics.SMGenerationExhaustion.coreFinite,
  GUT.SMGenerationExhaustion.exists_nonzero_bounded_factor_iff => Physics.SMGenerationExhaustion.exists_nonzero_bounded_factor_iff,
  GUT.SMGenerationExhaustion.exists_nonzero_factor_iff => Physics.SMGenerationExhaustion.exists_nonzero_factor_iff,
  GUT.SMGenerationExhaustion.exists_nonzero_occupation_iff => Physics.SMGenerationExhaustion.exists_nonzero_occupation_iff,
  GUT.SMGenerationExhaustion.factor => Physics.SMGenerationExhaustion.factor,
  GUT.SMGenerationExhaustion.factorFinite => Physics.SMGenerationExhaustion.factorFinite,
  GUT.SMGenerationExhaustion.factor_dimension => Physics.SMGenerationExhaustion.factor_dimension,
  GUT.SMGenerationExhaustion.leaves => Physics.SMGenerationExhaustion.leaves,
  GUT.SMGenerationExhaustion.nonzero_factor_fits => Physics.SMGenerationExhaustion.nonzero_factor_fits,
  GUT.SMGenerationExhaustion.occupationEquiv => Physics.SMGenerationExhaustion.occupationEquiv,
  GUT.SMGenerationExhaustion.source_nonzero_iff => Physics.SMGenerationExhaustion.source_nonzero_iff
]

assert_compatible GUT.SMGenerationExhaustion.Core => Physics.SMGenerationExhaustion.Core
assert_compatible GUT.SMGenerationExhaustion.FactorCarrier => Physics.SMGenerationExhaustion.FactorCarrier
assert_compatible GUT.SMGenerationExhaustion.Fits => Physics.SMGenerationExhaustion.Fits
assert_compatible GUT.SMGenerationExhaustion.Fits.eq_1 => Physics.SMGenerationExhaustion.Fits.eq_1
assert_compatible GUT.SMGenerationExhaustion.Occupation => Physics.SMGenerationExhaustion.Occupation
assert_compatible GUT.SMGenerationExhaustion.actual_field => Physics.SMGenerationExhaustion.actual_field
assert_compatible GUT.SMGenerationExhaustion.core => Physics.SMGenerationExhaustion.core
assert_compatible GUT.SMGenerationExhaustion.coreFinite => Physics.SMGenerationExhaustion.coreFinite
assert_compatible GUT.SMGenerationExhaustion.exists_nonzero_bounded_factor_iff => Physics.SMGenerationExhaustion.exists_nonzero_bounded_factor_iff
assert_compatible GUT.SMGenerationExhaustion.exists_nonzero_factor_iff => Physics.SMGenerationExhaustion.exists_nonzero_factor_iff
assert_compatible GUT.SMGenerationExhaustion.exists_nonzero_occupation_iff => Physics.SMGenerationExhaustion.exists_nonzero_occupation_iff
assert_compatible GUT.SMGenerationExhaustion.factor => Physics.SMGenerationExhaustion.factor
assert_compatible GUT.SMGenerationExhaustion.factorFinite => Physics.SMGenerationExhaustion.factorFinite
assert_compatible GUT.SMGenerationExhaustion.factor_dimension => Physics.SMGenerationExhaustion.factor_dimension
assert_compatible GUT.SMGenerationExhaustion.leaves => Physics.SMGenerationExhaustion.leaves
assert_compatible GUT.SMGenerationExhaustion.nonzero_factor_fits => Physics.SMGenerationExhaustion.nonzero_factor_fits
assert_compatible GUT.SMGenerationExhaustion.occupationEquiv => Physics.SMGenerationExhaustion.occupationEquiv
assert_compatible GUT.SMGenerationExhaustion.source_nonzero_iff => Physics.SMGenerationExhaustion.source_nonzero_iff
