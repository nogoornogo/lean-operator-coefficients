import Physics.StandardModel.Operators.Support.Lepton.SMLContinuousCharacter
import Physics.StandardModel.Operators.SMLWeightExpansion
import Math.RepresentationTheory.ExteriorContinuity
import Math.RepresentationTheory.SL2SpanContinuity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLContinuousCharacter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLContinuousCharacter.bosonAction => Physics.SMLContinuousCharacter.bosonAction,
  GUT.SMLContinuousCharacter.bosonEquiv => Physics.SMLContinuousCharacter.bosonEquiv,
  GUT.SMLContinuousCharacter.bosonModel => Physics.SMLContinuousCharacter.bosonModel,
  GUT.SMLContinuousCharacter.boson_apply => Physics.SMLContinuousCharacter.boson_apply,
  GUT.SMLContinuousCharacter.boson_continuous => Physics.SMLContinuousCharacter.boson_continuous,
  GUT.SMLContinuousCharacter.coefficient_dimension => Physics.SMLContinuousCharacter.coefficient_dimension,
  GUT.SMLContinuousCharacter.continuous_model => Physics.SMLContinuousCharacter.continuous_model,
  GUT.SMLContinuousCharacter.equiv => Physics.SMLContinuousCharacter.equiv,
  GUT.SMLContinuousCharacter.exteriorModelEquiv => Physics.SMLContinuousCharacter.exteriorModelEquiv,
  GUT.SMLContinuousCharacter.fieldAction => Physics.SMLContinuousCharacter.fieldAction,
  GUT.SMLContinuousCharacter.fieldCopy => Physics.SMLContinuousCharacter.fieldCopy,
  GUT.SMLContinuousCharacter.fieldFinite => Physics.SMLContinuousCharacter.fieldFinite,
  GUT.SMLContinuousCharacter.field_basis_coordinates => Physics.SMLContinuousCharacter.field_basis_coordinates,
  GUT.SMLContinuousCharacter.field_continuous => Physics.SMLContinuousCharacter.field_continuous,
  GUT.SMLContinuousCharacter.model => Physics.SMLContinuousCharacter.model,
  GUT.SMLContinuousCharacter.sourceAction => Physics.SMLContinuousCharacter.sourceAction,
  GUT.SMLContinuousCharacter.sourceBasis => Physics.SMLContinuousCharacter.sourceBasis,
  GUT.SMLContinuousCharacter.sourceCopy => Physics.SMLContinuousCharacter.sourceCopy,
  GUT.SMLContinuousCharacter.sourceFinite => Physics.SMLContinuousCharacter.sourceFinite,
  GUT.SMLContinuousCharacter.sourceModel => Physics.SMLContinuousCharacter.sourceModel,
  GUT.SMLContinuousCharacter.source_continuous => Physics.SMLContinuousCharacter.source_continuous,
  GUT.SMLContinuousCharacter.weights => Physics.SMLContinuousCharacter.weights,
  GUT.SMLWeightExpansion.pairInclusion.eq_1 => Physics.SMLWeightExpansion.pairInclusion.eq_1
]

assert_compatible GUT.SMLContinuousCharacter.bosonAction => Physics.SMLContinuousCharacter.bosonAction
assert_compatible GUT.SMLContinuousCharacter.bosonEquiv => Physics.SMLContinuousCharacter.bosonEquiv
assert_compatible GUT.SMLContinuousCharacter.bosonModel => Physics.SMLContinuousCharacter.bosonModel
assert_compatible GUT.SMLContinuousCharacter.boson_apply => Physics.SMLContinuousCharacter.boson_apply
assert_compatible GUT.SMLContinuousCharacter.boson_continuous => Physics.SMLContinuousCharacter.boson_continuous
assert_compatible GUT.SMLContinuousCharacter.coefficient_dimension => Physics.SMLContinuousCharacter.coefficient_dimension
assert_compatible GUT.SMLContinuousCharacter.continuous_model => Physics.SMLContinuousCharacter.continuous_model
assert_compatible GUT.SMLContinuousCharacter.equiv => Physics.SMLContinuousCharacter.equiv
assert_compatible GUT.SMLContinuousCharacter.exteriorModelEquiv => Physics.SMLContinuousCharacter.exteriorModelEquiv
assert_compatible GUT.SMLContinuousCharacter.fieldAction => Physics.SMLContinuousCharacter.fieldAction
assert_compatible GUT.SMLContinuousCharacter.fieldCopy => Physics.SMLContinuousCharacter.fieldCopy
assert_compatible GUT.SMLContinuousCharacter.fieldFinite => Physics.SMLContinuousCharacter.fieldFinite
assert_compatible GUT.SMLContinuousCharacter.field_basis_coordinates => Physics.SMLContinuousCharacter.field_basis_coordinates
assert_compatible GUT.SMLContinuousCharacter.field_continuous => Physics.SMLContinuousCharacter.field_continuous
assert_compatible GUT.SMLContinuousCharacter.model => Physics.SMLContinuousCharacter.model
assert_compatible GUT.SMLContinuousCharacter.sourceAction => Physics.SMLContinuousCharacter.sourceAction
assert_compatible GUT.SMLContinuousCharacter.sourceBasis => Physics.SMLContinuousCharacter.sourceBasis
assert_compatible GUT.SMLContinuousCharacter.sourceCopy => Physics.SMLContinuousCharacter.sourceCopy
assert_compatible GUT.SMLContinuousCharacter.sourceFinite => Physics.SMLContinuousCharacter.sourceFinite
assert_compatible GUT.SMLContinuousCharacter.sourceModel => Physics.SMLContinuousCharacter.sourceModel
assert_compatible GUT.SMLContinuousCharacter.source_continuous => Physics.SMLContinuousCharacter.source_continuous
assert_compatible GUT.SMLContinuousCharacter.weights => Physics.SMLContinuousCharacter.weights
assert_compatible GUT.SMLWeightExpansion.pairInclusion.eq_1 => Physics.SMLWeightExpansion.pairInclusion.eq_1
