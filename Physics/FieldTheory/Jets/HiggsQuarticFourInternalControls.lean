import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalControls
import Physics.FieldTheory.Jets.HiggsQuarticFourInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFieldDictionary.higgs.eq_1 => Physics.HiggsFieldDictionary.higgs.eq_1,
  GUT.HiggsQuarticFourInternalControls.T => Physics.HiggsQuarticFourInternalControls.T,
  GUT.HiggsQuarticFourInternalControls.eigen => Physics.HiggsQuarticFourInternalControls.eigen,
  GUT.HiggsQuarticFourInternalControls.eigen.eq_1 => Physics.HiggsQuarticFourInternalControls.eigen.eq_1,
  GUT.HiggsQuarticFourInternalControls.field => Physics.HiggsQuarticFourInternalControls.field,
  GUT.HiggsQuarticFourInternalControls.flipGroup => Physics.HiggsQuarticFourInternalControls.flipGroup,
  GUT.HiggsQuarticFourInternalControls.higgs_apply => Physics.HiggsQuarticFourInternalControls.higgs_apply,
  GUT.HiggsQuarticFourInternalControls.label => Physics.HiggsQuarticFourInternalControls.label,
  GUT.HiggsQuarticFourInternalControls.label.eq_1 => Physics.HiggsQuarticFourInternalControls.label.eq_1,
  GUT.HiggsQuarticFourInternalControls.label_surjective => Physics.HiggsQuarticFourInternalControls.label_surjective,
  GUT.HiggsQuarticFourInternalControls.numerator => Physics.HiggsQuarticFourInternalControls.numerator,
  GUT.HiggsQuarticFourInternalControls.numerator.eq_1 => Physics.HiggsQuarticFourInternalControls.numerator.eq_1,
  GUT.HiggsQuarticFourInternalControls.phaseCircle => Physics.HiggsQuarticFourInternalControls.phaseCircle,
  GUT.HiggsQuarticFourInternalControls.phaseCircle.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseCircle.eq_1,
  GUT.HiggsQuarticFourInternalControls.phaseGroup => Physics.HiggsQuarticFourInternalControls.phaseGroup,
  GUT.HiggsQuarticFourInternalControls.phaseGroup.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseGroup.eq_1,
  GUT.HiggsQuarticFourInternalControls.phaseWeak => Physics.HiggsQuarticFourInternalControls.phaseWeak,
  GUT.HiggsQuarticFourInternalControls.phaseWeak.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseWeak.eq_1,
  GUT.HiggsQuarticFourInternalControls.phase_action => Physics.HiggsQuarticFourInternalControls.phase_action,
  GUT.HiggsQuarticFourInternalControls.phase_backward => Physics.HiggsQuarticFourInternalControls.phase_backward,
  GUT.HiggsQuarticFourInternalControls.phase_field => Physics.HiggsQuarticFourInternalControls.phase_field,
  GUT.HiggsQuarticFourInternalControls.phase_forward => Physics.HiggsQuarticFourInternalControls.phase_forward,
  GUT.HiggsQuarticFourInternalControls.phase_value => Physics.HiggsQuarticFourInternalControls.phase_value,
  GUT.HiggsQuarticFourInternalControls.rotationGroup => Physics.HiggsQuarticFourInternalControls.rotationGroup,
  GUT.HiggsQuarticFourInternalControls.rotationGroup.eq_1 => Physics.HiggsQuarticFourInternalControls.rotationGroup.eq_1,
  GUT.HiggsQuarticFourInternalControls.rotationWeak => Physics.HiggsQuarticFourInternalControls.rotationWeak,
  GUT.HiggsQuarticFourInternalControls.rotationWeak.eq_1 => Physics.HiggsQuarticFourInternalControls.rotationWeak.eq_1,
  GUT.HiggsQuarticFourInternalControls.rotation_action => Physics.HiggsQuarticFourInternalControls.rotation_action,
  GUT.HiggsQuarticFourInternalControls.rotation_field => Physics.HiggsQuarticFourInternalControls.rotation_field,
  GUT.HiggsQuarticFourInternalControls.transport_eigen => Physics.HiggsQuarticFourInternalControls.transport_eigen,
  GUT.HiggsQuarticFourInternalControls.weight => Physics.HiggsQuarticFourInternalControls.weight,
  GUT.HiggsQuarticFourInternalControls.z => Physics.HiggsQuarticFourInternalControls.z,
  GUT.HiggsQuarticFourInternalControls.z.eq_1 => Physics.HiggsQuarticFourInternalControls.z.eq_1
]

assert_compatible GUT.HiggsFieldDictionary.higgs.eq_1 => Physics.HiggsFieldDictionary.higgs.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.T => Physics.HiggsQuarticFourInternalControls.T
assert_compatible GUT.HiggsQuarticFourInternalControls.eigen => Physics.HiggsQuarticFourInternalControls.eigen
assert_compatible GUT.HiggsQuarticFourInternalControls.eigen.eq_1 => Physics.HiggsQuarticFourInternalControls.eigen.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.field => Physics.HiggsQuarticFourInternalControls.field
assert_compatible GUT.HiggsQuarticFourInternalControls.flipGroup => Physics.HiggsQuarticFourInternalControls.flipGroup
assert_compatible GUT.HiggsQuarticFourInternalControls.higgs_apply => Physics.HiggsQuarticFourInternalControls.higgs_apply
assert_compatible GUT.HiggsQuarticFourInternalControls.label => Physics.HiggsQuarticFourInternalControls.label
assert_compatible GUT.HiggsQuarticFourInternalControls.label.eq_1 => Physics.HiggsQuarticFourInternalControls.label.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.label_surjective => Physics.HiggsQuarticFourInternalControls.label_surjective
assert_compatible GUT.HiggsQuarticFourInternalControls.numerator => Physics.HiggsQuarticFourInternalControls.numerator
assert_compatible GUT.HiggsQuarticFourInternalControls.numerator.eq_1 => Physics.HiggsQuarticFourInternalControls.numerator.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseCircle => Physics.HiggsQuarticFourInternalControls.phaseCircle
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseCircle.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseCircle.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseGroup => Physics.HiggsQuarticFourInternalControls.phaseGroup
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseGroup.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseGroup.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseWeak => Physics.HiggsQuarticFourInternalControls.phaseWeak
assert_compatible GUT.HiggsQuarticFourInternalControls.phaseWeak.eq_1 => Physics.HiggsQuarticFourInternalControls.phaseWeak.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.phase_action => Physics.HiggsQuarticFourInternalControls.phase_action
assert_compatible GUT.HiggsQuarticFourInternalControls.phase_backward => Physics.HiggsQuarticFourInternalControls.phase_backward
assert_compatible GUT.HiggsQuarticFourInternalControls.phase_field => Physics.HiggsQuarticFourInternalControls.phase_field
assert_compatible GUT.HiggsQuarticFourInternalControls.phase_forward => Physics.HiggsQuarticFourInternalControls.phase_forward
assert_compatible GUT.HiggsQuarticFourInternalControls.phase_value => Physics.HiggsQuarticFourInternalControls.phase_value
assert_compatible GUT.HiggsQuarticFourInternalControls.rotationGroup => Physics.HiggsQuarticFourInternalControls.rotationGroup
assert_compatible GUT.HiggsQuarticFourInternalControls.rotationGroup.eq_1 => Physics.HiggsQuarticFourInternalControls.rotationGroup.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.rotationWeak => Physics.HiggsQuarticFourInternalControls.rotationWeak
assert_compatible GUT.HiggsQuarticFourInternalControls.rotationWeak.eq_1 => Physics.HiggsQuarticFourInternalControls.rotationWeak.eq_1
assert_compatible GUT.HiggsQuarticFourInternalControls.rotation_action => Physics.HiggsQuarticFourInternalControls.rotation_action
assert_compatible GUT.HiggsQuarticFourInternalControls.rotation_field => Physics.HiggsQuarticFourInternalControls.rotation_field
assert_compatible GUT.HiggsQuarticFourInternalControls.transport_eigen => Physics.HiggsQuarticFourInternalControls.transport_eigen
assert_compatible GUT.HiggsQuarticFourInternalControls.weight => Physics.HiggsQuarticFourInternalControls.weight
assert_compatible GUT.HiggsQuarticFourInternalControls.z => Physics.HiggsQuarticFourInternalControls.z
assert_compatible GUT.HiggsQuarticFourInternalControls.z.eq_1 => Physics.HiggsQuarticFourInternalControls.z.eq_1
