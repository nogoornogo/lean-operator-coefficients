import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockCoordinates
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkBlockCoordinates.Blocks => Physics.LiSixQuarkBlockCoordinates.Blocks,
  GUT.LiSixQuarkBlockCoordinates.Split => Physics.LiSixQuarkBlockCoordinates.Split,
  GUT.LiSixQuarkBlockCoordinates.V2 => Physics.LiSixQuarkBlockCoordinates.V2,
  GUT.LiSixQuarkBlockCoordinates.V3 => Physics.LiSixQuarkBlockCoordinates.V3,
  GUT.LiSixQuarkBlockCoordinates.colorAssemble => Physics.LiSixQuarkBlockCoordinates.colorAssemble,
  GUT.LiSixQuarkBlockCoordinates.colorAssemble.eq_1 => Physics.LiSixQuarkBlockCoordinates.colorAssemble.eq_1,
  GUT.LiSixQuarkBlockCoordinates.colorEquiv => Physics.LiSixQuarkBlockCoordinates.colorEquiv,
  GUT.LiSixQuarkBlockCoordinates.colorExtract => Physics.LiSixQuarkBlockCoordinates.colorExtract,
  GUT.LiSixQuarkBlockCoordinates.colorExtract.eq_1 => Physics.LiSixQuarkBlockCoordinates.colorExtract.eq_1,
  GUT.LiSixQuarkBlockCoordinates.color_pair => Physics.LiSixQuarkBlockCoordinates.color_pair,
  GUT.LiSixQuarkBlockCoordinates.localBlocks => Physics.LiSixQuarkBlockCoordinates.localBlocks,
  GUT.LiSixQuarkBlockCoordinates.spinAssemble => Physics.LiSixQuarkBlockCoordinates.spinAssemble,
  GUT.LiSixQuarkBlockCoordinates.spinAssemble.eq_1 => Physics.LiSixQuarkBlockCoordinates.spinAssemble.eq_1,
  GUT.LiSixQuarkBlockCoordinates.spinEquiv => Physics.LiSixQuarkBlockCoordinates.spinEquiv,
  GUT.LiSixQuarkBlockCoordinates.spinExtract => Physics.LiSixQuarkBlockCoordinates.spinExtract,
  GUT.LiSixQuarkBlockCoordinates.spinExtract.eq_1 => Physics.LiSixQuarkBlockCoordinates.spinExtract.eq_1,
  GUT.LiSixQuarkBlockCoordinates.spin_pair => Physics.LiSixQuarkBlockCoordinates.spin_pair,
  GUT.LiSixQuarkBlockCoordinates.transpose => Physics.LiSixQuarkBlockCoordinates.transpose
]

assert_compatible GUT.LiSixQuarkBlockCoordinates.Blocks => Physics.LiSixQuarkBlockCoordinates.Blocks
assert_compatible GUT.LiSixQuarkBlockCoordinates.Split => Physics.LiSixQuarkBlockCoordinates.Split
assert_compatible GUT.LiSixQuarkBlockCoordinates.V2 => Physics.LiSixQuarkBlockCoordinates.V2
assert_compatible GUT.LiSixQuarkBlockCoordinates.V3 => Physics.LiSixQuarkBlockCoordinates.V3
assert_compatible GUT.LiSixQuarkBlockCoordinates.colorAssemble => Physics.LiSixQuarkBlockCoordinates.colorAssemble
assert_compatible GUT.LiSixQuarkBlockCoordinates.colorAssemble.eq_1 => Physics.LiSixQuarkBlockCoordinates.colorAssemble.eq_1
assert_compatible GUT.LiSixQuarkBlockCoordinates.colorEquiv => Physics.LiSixQuarkBlockCoordinates.colorEquiv
assert_compatible GUT.LiSixQuarkBlockCoordinates.colorExtract => Physics.LiSixQuarkBlockCoordinates.colorExtract
assert_compatible GUT.LiSixQuarkBlockCoordinates.colorExtract.eq_1 => Physics.LiSixQuarkBlockCoordinates.colorExtract.eq_1
assert_compatible GUT.LiSixQuarkBlockCoordinates.color_pair => Physics.LiSixQuarkBlockCoordinates.color_pair
assert_compatible GUT.LiSixQuarkBlockCoordinates.localBlocks => Physics.LiSixQuarkBlockCoordinates.localBlocks
assert_compatible GUT.LiSixQuarkBlockCoordinates.spinAssemble => Physics.LiSixQuarkBlockCoordinates.spinAssemble
assert_compatible GUT.LiSixQuarkBlockCoordinates.spinAssemble.eq_1 => Physics.LiSixQuarkBlockCoordinates.spinAssemble.eq_1
assert_compatible GUT.LiSixQuarkBlockCoordinates.spinEquiv => Physics.LiSixQuarkBlockCoordinates.spinEquiv
assert_compatible GUT.LiSixQuarkBlockCoordinates.spinExtract => Physics.LiSixQuarkBlockCoordinates.spinExtract
assert_compatible GUT.LiSixQuarkBlockCoordinates.spinExtract.eq_1 => Physics.LiSixQuarkBlockCoordinates.spinExtract.eq_1
assert_compatible GUT.LiSixQuarkBlockCoordinates.spin_pair => Physics.LiSixQuarkBlockCoordinates.spin_pair
assert_compatible GUT.LiSixQuarkBlockCoordinates.transpose => Physics.LiSixQuarkBlockCoordinates.transpose
