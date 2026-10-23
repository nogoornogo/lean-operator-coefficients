import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Basic
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalUpper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Basic instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.K => Physics.HiggsFirstInternal.K,
  GUT.HiggsFirstInternal.K_apply => Physics.HiggsFirstInternal.K_apply,
  GUT.HiggsFirstInternal.V => Physics.HiggsFirstInternal.V,
  GUT.HiggsFirstInternal.mono => Physics.HiggsFirstInternal.mono,
  GUT.HiggsFirstInternal.mono.eq_1 => Physics.HiggsFirstInternal.mono.eq_1,
  GUT.HiggsFirstInternal.mono_grade => Physics.HiggsFirstInternal.mono_grade,
  GUT.HiggsFirstInternal.normalK => Physics.HiggsFirstInternal.normalK,
  GUT.HiggsFirstInternal.normal_form => Physics.HiggsFirstInternal.normal_form,
  GUT.HiggsFirstInternal.normalize => Physics.HiggsFirstInternal.normalize,
  GUT.HiggsFirstInternal.ordered => Physics.HiggsFirstInternal.ordered,
  GUT.HiggsFirstInternal.rotation_value => Physics.HiggsFirstInternal.rotation_value,
  GUT.HiggsFirstInternal.vanish => Physics.HiggsFirstInternal.vanish
]

assert_compatible GUT.HiggsFirstInternal.K => Physics.HiggsFirstInternal.K
assert_compatible GUT.HiggsFirstInternal.K_apply => Physics.HiggsFirstInternal.K_apply
assert_compatible GUT.HiggsFirstInternal.V => Physics.HiggsFirstInternal.V
assert_compatible GUT.HiggsFirstInternal.mono => Physics.HiggsFirstInternal.mono
assert_compatible GUT.HiggsFirstInternal.mono.eq_1 => Physics.HiggsFirstInternal.mono.eq_1
assert_compatible GUT.HiggsFirstInternal.mono_grade => Physics.HiggsFirstInternal.mono_grade
assert_compatible GUT.HiggsFirstInternal.normalK => Physics.HiggsFirstInternal.normalK
assert_compatible GUT.HiggsFirstInternal.normal_form => Physics.HiggsFirstInternal.normal_form
assert_compatible GUT.HiggsFirstInternal.normalize => Physics.HiggsFirstInternal.normalize
assert_compatible GUT.HiggsFirstInternal.ordered => Physics.HiggsFirstInternal.ordered
assert_compatible GUT.HiggsFirstInternal.rotation_value => Physics.HiggsFirstInternal.rotation_value
assert_compatible GUT.HiggsFirstInternal.vanish => Physics.HiggsFirstInternal.vanish
