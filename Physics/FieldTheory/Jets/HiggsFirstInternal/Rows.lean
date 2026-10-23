import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Rows
import Physics.FieldTheory.Jets.HiggsFirstInternal.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Rows instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.normalK.eq_1 => Physics.HiggsFirstInternal.normalK.eq_1,
  GUT.HiggsFirstInternal.ordered.eq_1 => Physics.HiggsFirstInternal.ordered.eq_1,
  GUT.HiggsFirstInternal.row0 => Physics.HiggsFirstInternal.row0,
  GUT.HiggsFirstInternal.row1 => Physics.HiggsFirstInternal.row1,
  GUT.HiggsFirstInternal.row2 => Physics.HiggsFirstInternal.row2,
  GUT.HiggsFirstInternal.row3 => Physics.HiggsFirstInternal.row3,
  GUT.HiggsFirstInternal.row4 => Physics.HiggsFirstInternal.row4,
  GUT.HiggsFirstInternal.row5 => Physics.HiggsFirstInternal.row5,
  GUT.HiggsFirstInternal.value0123 => Physics.HiggsFirstInternal.value0123,
  GUT.HiggsFirstInternal.value1023 => Physics.HiggsFirstInternal.value1023,
  GUT.HiggsFirstInternal.value1133 => Physics.HiggsFirstInternal.value1133,
  GUT.HiggsFirstInternal.value2013 => Physics.HiggsFirstInternal.value2013,
  GUT.HiggsFirstInternal.value3012 => Physics.HiggsFirstInternal.value3012,
  GUT.HiggsFirstInternal.value3113 => Physics.HiggsFirstInternal.value3113,
  GUT.HiggsQuarticFourInternalControls.weight.eq_1 => Physics.HiggsQuarticFourInternalControls.weight.eq_1
]

assert_compatible GUT.HiggsFirstInternal.normalK.eq_1 => Physics.HiggsFirstInternal.normalK.eq_1
assert_compatible GUT.HiggsFirstInternal.ordered.eq_1 => Physics.HiggsFirstInternal.ordered.eq_1
assert_compatible GUT.HiggsFirstInternal.row0 => Physics.HiggsFirstInternal.row0
assert_compatible GUT.HiggsFirstInternal.row1 => Physics.HiggsFirstInternal.row1
assert_compatible GUT.HiggsFirstInternal.row2 => Physics.HiggsFirstInternal.row2
assert_compatible GUT.HiggsFirstInternal.row3 => Physics.HiggsFirstInternal.row3
assert_compatible GUT.HiggsFirstInternal.row4 => Physics.HiggsFirstInternal.row4
assert_compatible GUT.HiggsFirstInternal.row5 => Physics.HiggsFirstInternal.row5
assert_compatible GUT.HiggsFirstInternal.value0123 => Physics.HiggsFirstInternal.value0123
assert_compatible GUT.HiggsFirstInternal.value1023 => Physics.HiggsFirstInternal.value1023
assert_compatible GUT.HiggsFirstInternal.value1133 => Physics.HiggsFirstInternal.value1133
assert_compatible GUT.HiggsFirstInternal.value2013 => Physics.HiggsFirstInternal.value2013
assert_compatible GUT.HiggsFirstInternal.value3012 => Physics.HiggsFirstInternal.value3012
assert_compatible GUT.HiggsFirstInternal.value3113 => Physics.HiggsFirstInternal.value3113
assert_compatible GUT.HiggsQuarticFourInternalControls.weight.eq_1 => Physics.HiggsQuarticFourInternalControls.weight.eq_1
