import Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.SMCombinedCompactAction
import Math.RepresentationTheory.BasisActionContinuity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactContinuity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCombinedCompactContinuity.bosonEquiv => Physics.SMCombinedCompactContinuity.bosonEquiv,
  GUT.SMCombinedCompactContinuity.bosonModel => Physics.SMCombinedCompactContinuity.bosonModel,
  GUT.SMCombinedCompactContinuity.boson_continuous => Physics.SMCombinedCompactContinuity.boson_continuous,
  GUT.SMCombinedCompactContinuity.coefficientEquiv => Physics.SMCombinedCompactContinuity.coefficientEquiv,
  GUT.SMCombinedCompactContinuity.color_coefficients => Physics.SMCombinedCompactContinuity.color_coefficients,
  GUT.SMCombinedCompactContinuity.continuous_model => Physics.SMCombinedCompactContinuity.continuous_model,
  GUT.SMCombinedCompactContinuity.equiv => Physics.SMCombinedCompactContinuity.equiv,
  GUT.SMCombinedCompactContinuity.fieldFinite => Physics.SMCombinedCompactContinuity.fieldFinite,
  GUT.SMCombinedCompactContinuity.field_coefficients => Physics.SMCombinedCompactContinuity.field_coefficients,
  GUT.SMCombinedCompactContinuity.gauge_coefficients => Physics.SMCombinedCompactContinuity.gauge_coefficients,
  GUT.SMCombinedCompactContinuity.model => Physics.SMCombinedCompactContinuity.model,
  GUT.SMCombinedCompactContinuity.phase_continuous => Physics.SMCombinedCompactContinuity.phase_continuous,
  GUT.SMCombinedCompactContinuity.sourceBasis => Physics.SMCombinedCompactContinuity.sourceBasis,
  GUT.SMCombinedCompactContinuity.sourceFinite => Physics.SMCombinedCompactContinuity.sourceFinite,
  GUT.SMCombinedCompactContinuity.sourceModel => Physics.SMCombinedCompactContinuity.sourceModel,
  GUT.SMCombinedCompactContinuity.source_continuous => Physics.SMCombinedCompactContinuity.source_continuous,
  GUT.SMCombinedCompactContinuity.spin_coefficients => Physics.SMCombinedCompactContinuity.spin_coefficients,
  GUT.SMCombinedCompactContinuity.twist_coefficients => Physics.SMCombinedCompactContinuity.twist_coefficients,
  GUT.SMCombinedCompactContinuity.weakProjection => Physics.SMCombinedCompactContinuity.weakProjection,
  GUT.SMCombinedCompactContinuity.weak_coefficients => Physics.SMCombinedCompactContinuity.weak_coefficients,
  GUT.SMHiggsConstituents.character.eq_1 => Physics.SMHiggsConstituents.character.eq_1,
  GUT.SMHiggsConstituents.hyperProjection.eq_1 => Physics.SMHiggsConstituents.hyperProjection.eq_1
]

assert_compatible GUT.SMCombinedCompactContinuity.bosonEquiv => Physics.SMCombinedCompactContinuity.bosonEquiv
assert_compatible GUT.SMCombinedCompactContinuity.bosonModel => Physics.SMCombinedCompactContinuity.bosonModel
assert_compatible GUT.SMCombinedCompactContinuity.boson_continuous => Physics.SMCombinedCompactContinuity.boson_continuous
assert_compatible GUT.SMCombinedCompactContinuity.coefficientEquiv => Physics.SMCombinedCompactContinuity.coefficientEquiv
assert_compatible GUT.SMCombinedCompactContinuity.color_coefficients => Physics.SMCombinedCompactContinuity.color_coefficients
assert_compatible GUT.SMCombinedCompactContinuity.continuous_model => Physics.SMCombinedCompactContinuity.continuous_model
assert_compatible GUT.SMCombinedCompactContinuity.equiv => Physics.SMCombinedCompactContinuity.equiv
assert_compatible GUT.SMCombinedCompactContinuity.fieldFinite => Physics.SMCombinedCompactContinuity.fieldFinite
assert_compatible GUT.SMCombinedCompactContinuity.field_coefficients => Physics.SMCombinedCompactContinuity.field_coefficients
assert_compatible GUT.SMCombinedCompactContinuity.gauge_coefficients => Physics.SMCombinedCompactContinuity.gauge_coefficients
assert_compatible GUT.SMCombinedCompactContinuity.model => Physics.SMCombinedCompactContinuity.model
assert_compatible GUT.SMCombinedCompactContinuity.phase_continuous => Physics.SMCombinedCompactContinuity.phase_continuous
assert_compatible GUT.SMCombinedCompactContinuity.sourceBasis => Physics.SMCombinedCompactContinuity.sourceBasis
assert_compatible GUT.SMCombinedCompactContinuity.sourceFinite => Physics.SMCombinedCompactContinuity.sourceFinite
assert_compatible GUT.SMCombinedCompactContinuity.sourceModel => Physics.SMCombinedCompactContinuity.sourceModel
assert_compatible GUT.SMCombinedCompactContinuity.source_continuous => Physics.SMCombinedCompactContinuity.source_continuous
assert_compatible GUT.SMCombinedCompactContinuity.spin_coefficients => Physics.SMCombinedCompactContinuity.spin_coefficients
assert_compatible GUT.SMCombinedCompactContinuity.twist_coefficients => Physics.SMCombinedCompactContinuity.twist_coefficients
assert_compatible GUT.SMCombinedCompactContinuity.weakProjection => Physics.SMCombinedCompactContinuity.weakProjection
assert_compatible GUT.SMCombinedCompactContinuity.weak_coefficients => Physics.SMCombinedCompactContinuity.weak_coefficients
assert_compatible GUT.SMHiggsConstituents.character.eq_1 => Physics.SMHiggsConstituents.character.eq_1
assert_compatible GUT.SMHiggsConstituents.hyperProjection.eq_1 => Physics.SMHiggsConstituents.hyperProjection.eq_1
