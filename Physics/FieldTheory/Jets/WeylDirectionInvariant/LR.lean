import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LR
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.LR instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylDirectionInvariant.LR.components => Physics.WeylDirectionInvariant.LR.components,
  GUT.WeylDirectionInvariant.LR.row0 => Physics.WeylDirectionInvariant.LR.row0,
  GUT.WeylDirectionInvariant.LR.row1 => Physics.WeylDirectionInvariant.LR.row1,
  GUT.WeylDirectionInvariant.LR.row10 => Physics.WeylDirectionInvariant.LR.row10,
  GUT.WeylDirectionInvariant.LR.row11 => Physics.WeylDirectionInvariant.LR.row11,
  GUT.WeylDirectionInvariant.LR.row12 => Physics.WeylDirectionInvariant.LR.row12,
  GUT.WeylDirectionInvariant.LR.row13 => Physics.WeylDirectionInvariant.LR.row13,
  GUT.WeylDirectionInvariant.LR.row14 => Physics.WeylDirectionInvariant.LR.row14,
  GUT.WeylDirectionInvariant.LR.row2 => Physics.WeylDirectionInvariant.LR.row2,
  GUT.WeylDirectionInvariant.LR.row3 => Physics.WeylDirectionInvariant.LR.row3,
  GUT.WeylDirectionInvariant.LR.row4 => Physics.WeylDirectionInvariant.LR.row4,
  GUT.WeylDirectionInvariant.LR.row5 => Physics.WeylDirectionInvariant.LR.row5,
  GUT.WeylDirectionInvariant.LR.row6 => Physics.WeylDirectionInvariant.LR.row6,
  GUT.WeylDirectionInvariant.LR.row7 => Physics.WeylDirectionInvariant.LR.row7,
  GUT.WeylDirectionInvariant.LR.row8 => Physics.WeylDirectionInvariant.LR.row8,
  GUT.WeylDirectionInvariant.LR.row9 => Physics.WeylDirectionInvariant.LR.row9,
  GUT.WeylDirectionInvariant.LR.value001 => Physics.WeylDirectionInvariant.LR.value001,
  GUT.WeylDirectionInvariant.LR.value002 => Physics.WeylDirectionInvariant.LR.value002,
  GUT.WeylDirectionInvariant.LR.value003 => Physics.WeylDirectionInvariant.LR.value003,
  GUT.WeylDirectionInvariant.LR.value010 => Physics.WeylDirectionInvariant.LR.value010,
  GUT.WeylDirectionInvariant.LR.value011 => Physics.WeylDirectionInvariant.LR.value011,
  GUT.WeylDirectionInvariant.LR.value012 => Physics.WeylDirectionInvariant.LR.value012,
  GUT.WeylDirectionInvariant.LR.value013 => Physics.WeylDirectionInvariant.LR.value013,
  GUT.WeylDirectionInvariant.LR.value100 => Physics.WeylDirectionInvariant.LR.value100,
  GUT.WeylDirectionInvariant.LR.value101 => Physics.WeylDirectionInvariant.LR.value101,
  GUT.WeylDirectionInvariant.LR.value102 => Physics.WeylDirectionInvariant.LR.value102,
  GUT.WeylDirectionInvariant.LR.value103 => Physics.WeylDirectionInvariant.LR.value103,
  GUT.WeylDirectionInvariant.LR.value110 => Physics.WeylDirectionInvariant.LR.value110,
  GUT.WeylDirectionInvariant.LR.value111 => Physics.WeylDirectionInvariant.LR.value111,
  GUT.WeylDirectionInvariant.LR.value112 => Physics.WeylDirectionInvariant.LR.value112,
  GUT.WeylDirectionInvariant.LR.value113 => Physics.WeylDirectionInvariant.LR.value113
]

assert_compatible GUT.WeylDirectionInvariant.LR.components => Physics.WeylDirectionInvariant.LR.components
assert_compatible GUT.WeylDirectionInvariant.LR.row0 => Physics.WeylDirectionInvariant.LR.row0
assert_compatible GUT.WeylDirectionInvariant.LR.row1 => Physics.WeylDirectionInvariant.LR.row1
assert_compatible GUT.WeylDirectionInvariant.LR.row10 => Physics.WeylDirectionInvariant.LR.row10
assert_compatible GUT.WeylDirectionInvariant.LR.row11 => Physics.WeylDirectionInvariant.LR.row11
assert_compatible GUT.WeylDirectionInvariant.LR.row12 => Physics.WeylDirectionInvariant.LR.row12
assert_compatible GUT.WeylDirectionInvariant.LR.row13 => Physics.WeylDirectionInvariant.LR.row13
assert_compatible GUT.WeylDirectionInvariant.LR.row14 => Physics.WeylDirectionInvariant.LR.row14
assert_compatible GUT.WeylDirectionInvariant.LR.row2 => Physics.WeylDirectionInvariant.LR.row2
assert_compatible GUT.WeylDirectionInvariant.LR.row3 => Physics.WeylDirectionInvariant.LR.row3
assert_compatible GUT.WeylDirectionInvariant.LR.row4 => Physics.WeylDirectionInvariant.LR.row4
assert_compatible GUT.WeylDirectionInvariant.LR.row5 => Physics.WeylDirectionInvariant.LR.row5
assert_compatible GUT.WeylDirectionInvariant.LR.row6 => Physics.WeylDirectionInvariant.LR.row6
assert_compatible GUT.WeylDirectionInvariant.LR.row7 => Physics.WeylDirectionInvariant.LR.row7
assert_compatible GUT.WeylDirectionInvariant.LR.row8 => Physics.WeylDirectionInvariant.LR.row8
assert_compatible GUT.WeylDirectionInvariant.LR.row9 => Physics.WeylDirectionInvariant.LR.row9
assert_compatible GUT.WeylDirectionInvariant.LR.value001 => Physics.WeylDirectionInvariant.LR.value001
assert_compatible GUT.WeylDirectionInvariant.LR.value002 => Physics.WeylDirectionInvariant.LR.value002
assert_compatible GUT.WeylDirectionInvariant.LR.value003 => Physics.WeylDirectionInvariant.LR.value003
assert_compatible GUT.WeylDirectionInvariant.LR.value010 => Physics.WeylDirectionInvariant.LR.value010
assert_compatible GUT.WeylDirectionInvariant.LR.value011 => Physics.WeylDirectionInvariant.LR.value011
assert_compatible GUT.WeylDirectionInvariant.LR.value012 => Physics.WeylDirectionInvariant.LR.value012
assert_compatible GUT.WeylDirectionInvariant.LR.value013 => Physics.WeylDirectionInvariant.LR.value013
assert_compatible GUT.WeylDirectionInvariant.LR.value100 => Physics.WeylDirectionInvariant.LR.value100
assert_compatible GUT.WeylDirectionInvariant.LR.value101 => Physics.WeylDirectionInvariant.LR.value101
assert_compatible GUT.WeylDirectionInvariant.LR.value102 => Physics.WeylDirectionInvariant.LR.value102
assert_compatible GUT.WeylDirectionInvariant.LR.value103 => Physics.WeylDirectionInvariant.LR.value103
assert_compatible GUT.WeylDirectionInvariant.LR.value110 => Physics.WeylDirectionInvariant.LR.value110
assert_compatible GUT.WeylDirectionInvariant.LR.value111 => Physics.WeylDirectionInvariant.LR.value111
assert_compatible GUT.WeylDirectionInvariant.LR.value112 => Physics.WeylDirectionInvariant.LR.value112
assert_compatible GUT.WeylDirectionInvariant.LR.value113 => Physics.WeylDirectionInvariant.LR.value113
