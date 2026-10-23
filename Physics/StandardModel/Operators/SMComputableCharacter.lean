import Physics.StandardModel.Operators.Support.Decomposition.SMComputableCharacter
import Physics.StandardModel.Operators.SMComputableSlotWeights
import Physics.StandardModel.Operators.SMWeylExtractionInput
import Math.RepresentationTheory.ComputableWeightPolynomial
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMComputableCharacter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMComputableCharacter.bosonTerms => Physics.SMComputableCharacter.bosonTerms,
  GUT.SMComputableCharacter.bosonTerms.eq_1 => Physics.SMComputableCharacter.bosonTerms.eq_1,
  GUT.SMComputableCharacter.bosonWeight => Physics.SMComputableCharacter.bosonWeight,
  GUT.SMComputableCharacter.bosonWeight.eq_1 => Physics.SMComputableCharacter.bosonWeight.eq_1,
  GUT.SMComputableCharacter.boson_character => Physics.SMComputableCharacter.boson_character,
  GUT.SMComputableCharacter.boson_evaluation => Physics.SMComputableCharacter.boson_evaluation,
  GUT.SMComputableCharacter.compactBorel => Physics.SMComputableCharacter.compactBorel,
  GUT.SMComputableCharacter.compactMeasurable => Physics.SMComputableCharacter.compactMeasurable,
  GUT.SMComputableCharacter.exteriorTerms => Physics.SMComputableCharacter.exteriorTerms,
  GUT.SMComputableCharacter.exteriorTerms.eq_1 => Physics.SMComputableCharacter.exteriorTerms.eq_1,
  GUT.SMComputableCharacter.exterior_evaluation => Physics.SMComputableCharacter.exterior_evaluation,
  GUT.SMComputableCharacter.extraction_eq => Physics.SMComputableCharacter.extraction_eq,
  GUT.SMComputableCharacter.fieldFinite => Physics.SMComputableCharacter.fieldFinite,
  GUT.SMComputableCharacter.gaugeEquiv => Physics.SMComputableCharacter.gaugeEquiv,
  GUT.SMComputableCharacter.gaugeSize => Physics.SMComputableCharacter.gaugeSize,
  GUT.SMComputableCharacter.indexEquiv => Physics.SMComputableCharacter.indexEquiv,
  GUT.SMComputableCharacter.leaves => Physics.SMComputableCharacter.leaves,
  GUT.SMComputableCharacter.monomial_boson => Physics.SMComputableCharacter.monomial_boson,
  GUT.SMComputableCharacter.multiplicity => Physics.SMComputableCharacter.multiplicity,
  GUT.SMComputableCharacter.polynomial => Physics.SMComputableCharacter.polynomial,
  GUT.SMComputableCharacter.polynomial_coefficient => Physics.SMComputableCharacter.polynomial_coefficient,
  GUT.SMComputableCharacter.size => Physics.SMComputableCharacter.size,
  GUT.SMComputableCharacter.slotBasis => Physics.SMComputableCharacter.slotBasis,
  GUT.SMComputableCharacter.slotBasis.eq_1 => Physics.SMComputableCharacter.slotBasis.eq_1,
  GUT.SMComputableCharacter.slotWeight => Physics.SMComputableCharacter.slotWeight,
  GUT.SMComputableCharacter.slotWeight.eq_1 => Physics.SMComputableCharacter.slotWeight.eq_1,
  GUT.SMComputableCharacter.slot_eigen => Physics.SMComputableCharacter.slot_eigen,
  GUT.SMComputableCharacter.sourceFinite => Physics.SMComputableCharacter.sourceFinite,
  GUT.SMComputableCharacter.sourceTerms => Physics.SMComputableCharacter.sourceTerms,
  GUT.SMComputableCharacter.sourceTerms.eq_1 => Physics.SMComputableCharacter.sourceTerms.eq_1,
  GUT.SMComputableCharacter.source_evaluation => Physics.SMComputableCharacter.source_evaluation,
  GUT.SMComputableCharacter.terms => Physics.SMComputableCharacter.terms,
  GUT.SMComputableCharacter.terms_evaluation => Physics.SMComputableCharacter.terms_evaluation
]

assert_compatible GUT.SMComputableCharacter.bosonTerms => Physics.SMComputableCharacter.bosonTerms
assert_compatible GUT.SMComputableCharacter.bosonTerms.eq_1 => Physics.SMComputableCharacter.bosonTerms.eq_1
assert_compatible GUT.SMComputableCharacter.bosonWeight => Physics.SMComputableCharacter.bosonWeight
assert_compatible GUT.SMComputableCharacter.bosonWeight.eq_1 => Physics.SMComputableCharacter.bosonWeight.eq_1
assert_compatible GUT.SMComputableCharacter.boson_character => Physics.SMComputableCharacter.boson_character
assert_compatible GUT.SMComputableCharacter.boson_evaluation => Physics.SMComputableCharacter.boson_evaluation
assert_compatible GUT.SMComputableCharacter.compactBorel => Physics.SMComputableCharacter.compactBorel
assert_compatible GUT.SMComputableCharacter.compactMeasurable => Physics.SMComputableCharacter.compactMeasurable
assert_compatible GUT.SMComputableCharacter.exteriorTerms => Physics.SMComputableCharacter.exteriorTerms
assert_compatible GUT.SMComputableCharacter.exteriorTerms.eq_1 => Physics.SMComputableCharacter.exteriorTerms.eq_1
assert_compatible GUT.SMComputableCharacter.exterior_evaluation => Physics.SMComputableCharacter.exterior_evaluation
assert_compatible GUT.SMComputableCharacter.extraction_eq => Physics.SMComputableCharacter.extraction_eq
assert_compatible GUT.SMComputableCharacter.fieldFinite => Physics.SMComputableCharacter.fieldFinite
assert_compatible GUT.SMComputableCharacter.gaugeEquiv => Physics.SMComputableCharacter.gaugeEquiv
assert_compatible GUT.SMComputableCharacter.gaugeSize => Physics.SMComputableCharacter.gaugeSize
assert_compatible GUT.SMComputableCharacter.indexEquiv => Physics.SMComputableCharacter.indexEquiv
assert_compatible GUT.SMComputableCharacter.leaves => Physics.SMComputableCharacter.leaves
assert_compatible GUT.SMComputableCharacter.monomial_boson => Physics.SMComputableCharacter.monomial_boson
assert_compatible GUT.SMComputableCharacter.multiplicity => Physics.SMComputableCharacter.multiplicity
assert_compatible GUT.SMComputableCharacter.polynomial => Physics.SMComputableCharacter.polynomial
assert_compatible GUT.SMComputableCharacter.polynomial_coefficient => Physics.SMComputableCharacter.polynomial_coefficient
assert_compatible GUT.SMComputableCharacter.size => Physics.SMComputableCharacter.size
assert_compatible GUT.SMComputableCharacter.slotBasis => Physics.SMComputableCharacter.slotBasis
assert_compatible GUT.SMComputableCharacter.slotBasis.eq_1 => Physics.SMComputableCharacter.slotBasis.eq_1
assert_compatible GUT.SMComputableCharacter.slotWeight => Physics.SMComputableCharacter.slotWeight
assert_compatible GUT.SMComputableCharacter.slotWeight.eq_1 => Physics.SMComputableCharacter.slotWeight.eq_1
assert_compatible GUT.SMComputableCharacter.slot_eigen => Physics.SMComputableCharacter.slot_eigen
assert_compatible GUT.SMComputableCharacter.sourceFinite => Physics.SMComputableCharacter.sourceFinite
assert_compatible GUT.SMComputableCharacter.sourceTerms => Physics.SMComputableCharacter.sourceTerms
assert_compatible GUT.SMComputableCharacter.sourceTerms.eq_1 => Physics.SMComputableCharacter.sourceTerms.eq_1
assert_compatible GUT.SMComputableCharacter.source_evaluation => Physics.SMComputableCharacter.source_evaluation
assert_compatible GUT.SMComputableCharacter.terms => Physics.SMComputableCharacter.terms
assert_compatible GUT.SMComputableCharacter.terms_evaluation => Physics.SMComputableCharacter.terms_evaluation
