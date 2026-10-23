import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedFields
import Physics.StandardModel.Operators.DeltaLOneSignedInput
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Physics.FieldTheory.Spinor.OddWeylInvariant
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedFields instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaLOneSignedFields.Field => Physics.DeltaLOneSignedFields.Field,
  GUT.DeltaLOneSignedFields.GaugeCarrier => Physics.DeltaLOneSignedFields.GaugeCarrier,
  GUT.DeltaLOneSignedFields.Sector => Physics.DeltaLOneSignedFields.Sector,
  GUT.DeltaLOneSignedFields.admissible_of_nonzero => Physics.DeltaLOneSignedFields.admissible_of_nonzero,
  GUT.DeltaLOneSignedFields.baryonDegree_of_nonzero => Physics.DeltaLOneSignedFields.baryonDegree_of_nonzero,
  GUT.DeltaLOneSignedFields.centerElement => Physics.DeltaLOneSignedFields.centerElement,
  GUT.DeltaLOneSignedFields.centerElement.congr_simp => Physics.DeltaLOneSignedFields.centerElement.congr_simp,
  GUT.DeltaLOneSignedFields.centerElement.eq_1 => Physics.DeltaLOneSignedFields.centerElement.eq_1,
  GUT.DeltaLOneSignedFields.colorCenter => Physics.DeltaLOneSignedFields.colorCenter,
  GUT.DeltaLOneSignedFields.colorCenter.congr_simp => Physics.DeltaLOneSignedFields.colorCenter.congr_simp,
  GUT.DeltaLOneSignedFields.colorCenter.eq_1 => Physics.DeltaLOneSignedFields.colorCenter.eq_1,
  GUT.DeltaLOneSignedFields.even_leftSlots_of_nonzero => Physics.DeltaLOneSignedFields.even_leftSlots_of_nonzero,
  GUT.DeltaLOneSignedFields.field => Physics.DeltaLOneSignedFields.field,
  GUT.DeltaLOneSignedFields.field.eq_1 => Physics.DeltaLOneSignedFields.field.eq_1,
  GUT.DeltaLOneSignedFields.field_center => Physics.DeltaLOneSignedFields.field_center,
  GUT.DeltaLOneSignedFields.field_hypercharge => Physics.DeltaLOneSignedFields.field_hypercharge,
  GUT.DeltaLOneSignedFields.field_spin_basis => Physics.DeltaLOneSignedFields.field_spin_basis,
  GUT.DeltaLOneSignedFields.four_candidates => Physics.DeltaLOneSignedFields.four_candidates,
  GUT.DeltaLOneSignedFields.fullCenter => Physics.DeltaLOneSignedFields.fullCenter,
  GUT.DeltaLOneSignedFields.fullCenter.eq_1 => Physics.DeltaLOneSignedFields.fullCenter.eq_1,
  GUT.DeltaLOneSignedFields.fullHypercharge => Physics.DeltaLOneSignedFields.fullHypercharge,
  GUT.DeltaLOneSignedFields.fullHypercharge.eq_1 => Physics.DeltaLOneSignedFields.fullHypercharge.eq_1,
  GUT.DeltaLOneSignedFields.fullRepresentation => Physics.DeltaLOneSignedFields.fullRepresentation,
  GUT.DeltaLOneSignedFields.fullSpinTest => Physics.DeltaLOneSignedFields.fullSpinTest,
  GUT.DeltaLOneSignedFields.fullSpinTest.eq_1 => Physics.DeltaLOneSignedFields.fullSpinTest.eq_1,
  GUT.DeltaLOneSignedFields.gauge => Physics.DeltaLOneSignedFields.gauge,
  GUT.DeltaLOneSignedFields.gauge_candidates => Physics.DeltaLOneSignedFields.gauge_candidates,
  GUT.DeltaLOneSignedFields.gauge_center => Physics.DeltaLOneSignedFields.gauge_center,
  GUT.DeltaLOneSignedFields.gauge_hypercharge => Physics.DeltaLOneSignedFields.gauge_hypercharge,
  GUT.DeltaLOneSignedFields.hyperchargeElement => Physics.DeltaLOneSignedFields.hyperchargeElement,
  GUT.DeltaLOneSignedFields.hyperchargeElement.eq_1 => Physics.DeltaLOneSignedFields.hyperchargeElement.eq_1,
  GUT.DeltaLOneSignedFields.hypercharge_of_nonzero => Physics.DeltaLOneSignedFields.hypercharge_of_nonzero,
  GUT.DeltaLOneSignedFields.instAddCommGroupField => Physics.DeltaLOneSignedFields.instAddCommGroupField,
  GUT.DeltaLOneSignedFields.instAddCommGroupGaugeCarrier => Physics.DeltaLOneSignedFields.instAddCommGroupGaugeCarrier,
  GUT.DeltaLOneSignedFields.instModuleComplexGaugeCarrier => Physics.DeltaLOneSignedFields.instModuleComplexGaugeCarrier,
  GUT.DeltaLOneSignedFields.leftSlots_counts => Physics.DeltaLOneSignedFields.leftSlots_counts,
  GUT.DeltaLOneSignedFields.localField => Physics.DeltaLOneSignedFields.localField,
  GUT.DeltaLOneSignedFields.localField.eq_1 => Physics.DeltaLOneSignedFields.localField.eq_1,
  GUT.DeltaLOneSignedFields.no_conjugates_of_nonzero => Physics.DeltaLOneSignedFields.no_conjugates_of_nonzero,
  GUT.DeltaLOneSignedFields.odd_basis_vanish => Physics.DeltaLOneSignedFields.odd_basis_vanish,
  GUT.DeltaLOneSignedFields.odd_restriction_vanish => Physics.DeltaLOneSignedFields.odd_restriction_vanish,
  GUT.DeltaLOneSignedFields.rightHanded => Physics.DeltaLOneSignedFields.rightHanded,
  GUT.DeltaLOneSignedFields.rightHanded.eq_1 => Physics.DeltaLOneSignedFields.rightHanded.eq_1,
  GUT.DeltaLOneSignedFields.trialityRoot => Physics.DeltaLOneSignedFields.trialityRoot,
  GUT.DeltaLOneSignedFields.trialityRoot.eq_1 => Physics.DeltaLOneSignedFields.trialityRoot.eq_1,
  GUT.DeltaLOneSignedFields.trialityRoot_primitive => Physics.DeltaLOneSignedFields.trialityRoot_primitive,
  GUT.DeltaLOneSignedFields.triality_of_nonzero => Physics.DeltaLOneSignedFields.triality_of_nonzero,
  GUT.DeltaLOneSignedFields.vanish_outside_four => Physics.DeltaLOneSignedFields.vanish_outside_four
]

assert_compatible GUT.DeltaLOneSignedFields.Field => Physics.DeltaLOneSignedFields.Field
assert_compatible GUT.DeltaLOneSignedFields.GaugeCarrier => Physics.DeltaLOneSignedFields.GaugeCarrier
assert_compatible GUT.DeltaLOneSignedFields.Sector => Physics.DeltaLOneSignedFields.Sector
assert_compatible GUT.DeltaLOneSignedFields.admissible_of_nonzero => Physics.DeltaLOneSignedFields.admissible_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.baryonDegree_of_nonzero => Physics.DeltaLOneSignedFields.baryonDegree_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.centerElement => Physics.DeltaLOneSignedFields.centerElement
assert_compatible GUT.DeltaLOneSignedFields.centerElement.congr_simp => Physics.DeltaLOneSignedFields.centerElement.congr_simp
assert_compatible GUT.DeltaLOneSignedFields.centerElement.eq_1 => Physics.DeltaLOneSignedFields.centerElement.eq_1
assert_compatible GUT.DeltaLOneSignedFields.colorCenter => Physics.DeltaLOneSignedFields.colorCenter
assert_compatible GUT.DeltaLOneSignedFields.colorCenter.congr_simp => Physics.DeltaLOneSignedFields.colorCenter.congr_simp
assert_compatible GUT.DeltaLOneSignedFields.colorCenter.eq_1 => Physics.DeltaLOneSignedFields.colorCenter.eq_1
assert_compatible GUT.DeltaLOneSignedFields.even_leftSlots_of_nonzero => Physics.DeltaLOneSignedFields.even_leftSlots_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.field => Physics.DeltaLOneSignedFields.field
assert_compatible GUT.DeltaLOneSignedFields.field.eq_1 => Physics.DeltaLOneSignedFields.field.eq_1
assert_compatible GUT.DeltaLOneSignedFields.field_center => Physics.DeltaLOneSignedFields.field_center
assert_compatible GUT.DeltaLOneSignedFields.field_hypercharge => Physics.DeltaLOneSignedFields.field_hypercharge
assert_compatible GUT.DeltaLOneSignedFields.field_spin_basis => Physics.DeltaLOneSignedFields.field_spin_basis
assert_compatible GUT.DeltaLOneSignedFields.four_candidates => Physics.DeltaLOneSignedFields.four_candidates
assert_compatible GUT.DeltaLOneSignedFields.fullCenter => Physics.DeltaLOneSignedFields.fullCenter
assert_compatible GUT.DeltaLOneSignedFields.fullCenter.eq_1 => Physics.DeltaLOneSignedFields.fullCenter.eq_1
assert_compatible GUT.DeltaLOneSignedFields.fullHypercharge => Physics.DeltaLOneSignedFields.fullHypercharge
assert_compatible GUT.DeltaLOneSignedFields.fullHypercharge.eq_1 => Physics.DeltaLOneSignedFields.fullHypercharge.eq_1
assert_compatible GUT.DeltaLOneSignedFields.fullRepresentation => Physics.DeltaLOneSignedFields.fullRepresentation
assert_compatible GUT.DeltaLOneSignedFields.fullSpinTest => Physics.DeltaLOneSignedFields.fullSpinTest
assert_compatible GUT.DeltaLOneSignedFields.fullSpinTest.eq_1 => Physics.DeltaLOneSignedFields.fullSpinTest.eq_1
assert_compatible GUT.DeltaLOneSignedFields.gauge => Physics.DeltaLOneSignedFields.gauge
assert_compatible GUT.DeltaLOneSignedFields.gauge_candidates => Physics.DeltaLOneSignedFields.gauge_candidates
assert_compatible GUT.DeltaLOneSignedFields.gauge_center => Physics.DeltaLOneSignedFields.gauge_center
assert_compatible GUT.DeltaLOneSignedFields.gauge_hypercharge => Physics.DeltaLOneSignedFields.gauge_hypercharge
assert_compatible GUT.DeltaLOneSignedFields.hyperchargeElement => Physics.DeltaLOneSignedFields.hyperchargeElement
assert_compatible GUT.DeltaLOneSignedFields.hyperchargeElement.eq_1 => Physics.DeltaLOneSignedFields.hyperchargeElement.eq_1
assert_compatible GUT.DeltaLOneSignedFields.hypercharge_of_nonzero => Physics.DeltaLOneSignedFields.hypercharge_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.instAddCommGroupField => Physics.DeltaLOneSignedFields.instAddCommGroupField
assert_compatible GUT.DeltaLOneSignedFields.instAddCommGroupGaugeCarrier => Physics.DeltaLOneSignedFields.instAddCommGroupGaugeCarrier
assert_compatible GUT.DeltaLOneSignedFields.instModuleComplexGaugeCarrier => Physics.DeltaLOneSignedFields.instModuleComplexGaugeCarrier
assert_compatible GUT.DeltaLOneSignedFields.leftSlots_counts => Physics.DeltaLOneSignedFields.leftSlots_counts
assert_compatible GUT.DeltaLOneSignedFields.localField => Physics.DeltaLOneSignedFields.localField
assert_compatible GUT.DeltaLOneSignedFields.localField.eq_1 => Physics.DeltaLOneSignedFields.localField.eq_1
assert_compatible GUT.DeltaLOneSignedFields.no_conjugates_of_nonzero => Physics.DeltaLOneSignedFields.no_conjugates_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.odd_basis_vanish => Physics.DeltaLOneSignedFields.odd_basis_vanish
assert_compatible GUT.DeltaLOneSignedFields.odd_restriction_vanish => Physics.DeltaLOneSignedFields.odd_restriction_vanish
assert_compatible GUT.DeltaLOneSignedFields.rightHanded => Physics.DeltaLOneSignedFields.rightHanded
assert_compatible GUT.DeltaLOneSignedFields.rightHanded.eq_1 => Physics.DeltaLOneSignedFields.rightHanded.eq_1
assert_compatible GUT.DeltaLOneSignedFields.trialityRoot => Physics.DeltaLOneSignedFields.trialityRoot
assert_compatible GUT.DeltaLOneSignedFields.trialityRoot.eq_1 => Physics.DeltaLOneSignedFields.trialityRoot.eq_1
assert_compatible GUT.DeltaLOneSignedFields.trialityRoot_primitive => Physics.DeltaLOneSignedFields.trialityRoot_primitive
assert_compatible GUT.DeltaLOneSignedFields.triality_of_nonzero => Physics.DeltaLOneSignedFields.triality_of_nonzero
assert_compatible GUT.DeltaLOneSignedFields.vanish_outside_four => Physics.DeltaLOneSignedFields.vanish_outside_four
