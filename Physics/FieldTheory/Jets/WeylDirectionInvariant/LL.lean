import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LL
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LL instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzFiniteControls.flipX.eq_1 => Physics.LorentzFiniteControls.flipX.eq_1,
  GUT.LorentzFiniteControls.flipZ.eq_1 => Physics.LorentzFiniteControls.flipZ.eq_1,
  GUT.WeylDirectionInvariant.LL.components => Physics.WeylDirectionInvariant.LL.components,
  GUT.WeylDirectionInvariant.LL.row0 => Physics.WeylDirectionInvariant.LL.row0,
  GUT.WeylDirectionInvariant.LL.row1 => Physics.WeylDirectionInvariant.LL.row1,
  GUT.WeylDirectionInvariant.LL.row10 => Physics.WeylDirectionInvariant.LL.row10,
  GUT.WeylDirectionInvariant.LL.row11 => Physics.WeylDirectionInvariant.LL.row11,
  GUT.WeylDirectionInvariant.LL.row12 => Physics.WeylDirectionInvariant.LL.row12,
  GUT.WeylDirectionInvariant.LL.row13 => Physics.WeylDirectionInvariant.LL.row13,
  GUT.WeylDirectionInvariant.LL.row14 => Physics.WeylDirectionInvariant.LL.row14,
  GUT.WeylDirectionInvariant.LL.row15 => Physics.WeylDirectionInvariant.LL.row15,
  GUT.WeylDirectionInvariant.LL.row2 => Physics.WeylDirectionInvariant.LL.row2,
  GUT.WeylDirectionInvariant.LL.row3 => Physics.WeylDirectionInvariant.LL.row3,
  GUT.WeylDirectionInvariant.LL.row4 => Physics.WeylDirectionInvariant.LL.row4,
  GUT.WeylDirectionInvariant.LL.row5 => Physics.WeylDirectionInvariant.LL.row5,
  GUT.WeylDirectionInvariant.LL.row6 => Physics.WeylDirectionInvariant.LL.row6,
  GUT.WeylDirectionInvariant.LL.row7 => Physics.WeylDirectionInvariant.LL.row7,
  GUT.WeylDirectionInvariant.LL.row8 => Physics.WeylDirectionInvariant.LL.row8,
  GUT.WeylDirectionInvariant.LL.row9 => Physics.WeylDirectionInvariant.LL.row9,
  GUT.WeylDirectionInvariant.LL.value000 => Physics.WeylDirectionInvariant.LL.value000,
  GUT.WeylDirectionInvariant.LL.value001 => Physics.WeylDirectionInvariant.LL.value001,
  GUT.WeylDirectionInvariant.LL.value002 => Physics.WeylDirectionInvariant.LL.value002,
  GUT.WeylDirectionInvariant.LL.value003 => Physics.WeylDirectionInvariant.LL.value003,
  GUT.WeylDirectionInvariant.LL.value010 => Physics.WeylDirectionInvariant.LL.value010,
  GUT.WeylDirectionInvariant.LL.value011 => Physics.WeylDirectionInvariant.LL.value011,
  GUT.WeylDirectionInvariant.LL.value012 => Physics.WeylDirectionInvariant.LL.value012,
  GUT.WeylDirectionInvariant.LL.value013 => Physics.WeylDirectionInvariant.LL.value013,
  GUT.WeylDirectionInvariant.LL.value100 => Physics.WeylDirectionInvariant.LL.value100,
  GUT.WeylDirectionInvariant.LL.value101 => Physics.WeylDirectionInvariant.LL.value101,
  GUT.WeylDirectionInvariant.LL.value102 => Physics.WeylDirectionInvariant.LL.value102,
  GUT.WeylDirectionInvariant.LL.value103 => Physics.WeylDirectionInvariant.LL.value103,
  GUT.WeylDirectionInvariant.LL.value110 => Physics.WeylDirectionInvariant.LL.value110,
  GUT.WeylDirectionInvariant.LL.value111 => Physics.WeylDirectionInvariant.LL.value111,
  GUT.WeylDirectionInvariant.LL.value112 => Physics.WeylDirectionInvariant.LL.value112,
  GUT.WeylDirectionInvariant.LL.value113 => Physics.WeylDirectionInvariant.LL.value113,
  GUT.WeylDirectionInvariant.kernel.eq_1 => Physics.WeylDirectionInvariant.kernel.eq_1,
  GUT.WeylDirectionInvariant.spinRows.eq_1 => Physics.WeylDirectionInvariant.spinRows.eq_1
]

assert_compatible GUT.LorentzFiniteControls.flipX.eq_1 => Physics.LorentzFiniteControls.flipX.eq_1
assert_compatible GUT.LorentzFiniteControls.flipZ.eq_1 => Physics.LorentzFiniteControls.flipZ.eq_1
assert_compatible GUT.WeylDirectionInvariant.LL.components => Physics.WeylDirectionInvariant.LL.components
assert_compatible GUT.WeylDirectionInvariant.LL.row0 => Physics.WeylDirectionInvariant.LL.row0
assert_compatible GUT.WeylDirectionInvariant.LL.row1 => Physics.WeylDirectionInvariant.LL.row1
assert_compatible GUT.WeylDirectionInvariant.LL.row10 => Physics.WeylDirectionInvariant.LL.row10
assert_compatible GUT.WeylDirectionInvariant.LL.row11 => Physics.WeylDirectionInvariant.LL.row11
assert_compatible GUT.WeylDirectionInvariant.LL.row12 => Physics.WeylDirectionInvariant.LL.row12
assert_compatible GUT.WeylDirectionInvariant.LL.row13 => Physics.WeylDirectionInvariant.LL.row13
assert_compatible GUT.WeylDirectionInvariant.LL.row14 => Physics.WeylDirectionInvariant.LL.row14
assert_compatible GUT.WeylDirectionInvariant.LL.row15 => Physics.WeylDirectionInvariant.LL.row15
assert_compatible GUT.WeylDirectionInvariant.LL.row2 => Physics.WeylDirectionInvariant.LL.row2
assert_compatible GUT.WeylDirectionInvariant.LL.row3 => Physics.WeylDirectionInvariant.LL.row3
assert_compatible GUT.WeylDirectionInvariant.LL.row4 => Physics.WeylDirectionInvariant.LL.row4
assert_compatible GUT.WeylDirectionInvariant.LL.row5 => Physics.WeylDirectionInvariant.LL.row5
assert_compatible GUT.WeylDirectionInvariant.LL.row6 => Physics.WeylDirectionInvariant.LL.row6
assert_compatible GUT.WeylDirectionInvariant.LL.row7 => Physics.WeylDirectionInvariant.LL.row7
assert_compatible GUT.WeylDirectionInvariant.LL.row8 => Physics.WeylDirectionInvariant.LL.row8
assert_compatible GUT.WeylDirectionInvariant.LL.row9 => Physics.WeylDirectionInvariant.LL.row9
assert_compatible GUT.WeylDirectionInvariant.LL.value000 => Physics.WeylDirectionInvariant.LL.value000
assert_compatible GUT.WeylDirectionInvariant.LL.value001 => Physics.WeylDirectionInvariant.LL.value001
assert_compatible GUT.WeylDirectionInvariant.LL.value002 => Physics.WeylDirectionInvariant.LL.value002
assert_compatible GUT.WeylDirectionInvariant.LL.value003 => Physics.WeylDirectionInvariant.LL.value003
assert_compatible GUT.WeylDirectionInvariant.LL.value010 => Physics.WeylDirectionInvariant.LL.value010
assert_compatible GUT.WeylDirectionInvariant.LL.value011 => Physics.WeylDirectionInvariant.LL.value011
assert_compatible GUT.WeylDirectionInvariant.LL.value012 => Physics.WeylDirectionInvariant.LL.value012
assert_compatible GUT.WeylDirectionInvariant.LL.value013 => Physics.WeylDirectionInvariant.LL.value013
assert_compatible GUT.WeylDirectionInvariant.LL.value100 => Physics.WeylDirectionInvariant.LL.value100
assert_compatible GUT.WeylDirectionInvariant.LL.value101 => Physics.WeylDirectionInvariant.LL.value101
assert_compatible GUT.WeylDirectionInvariant.LL.value102 => Physics.WeylDirectionInvariant.LL.value102
assert_compatible GUT.WeylDirectionInvariant.LL.value103 => Physics.WeylDirectionInvariant.LL.value103
assert_compatible GUT.WeylDirectionInvariant.LL.value110 => Physics.WeylDirectionInvariant.LL.value110
assert_compatible GUT.WeylDirectionInvariant.LL.value111 => Physics.WeylDirectionInvariant.LL.value111
assert_compatible GUT.WeylDirectionInvariant.LL.value112 => Physics.WeylDirectionInvariant.LL.value112
assert_compatible GUT.WeylDirectionInvariant.LL.value113 => Physics.WeylDirectionInvariant.LL.value113
assert_compatible GUT.WeylDirectionInvariant.kernel.eq_1 => Physics.WeylDirectionInvariant.kernel.eq_1
assert_compatible GUT.WeylDirectionInvariant.spinRows.eq_1 => Physics.WeylDirectionInvariant.spinRows.eq_1
