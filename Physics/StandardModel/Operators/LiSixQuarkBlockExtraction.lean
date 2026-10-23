import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockExtraction
import Physics.StandardModel.Operators.LiSixQuarkBlockAssembly
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockExtraction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkBlockAssembly.colorEntries.eq_1 => Physics.LiSixQuarkBlockAssembly.colorEntries.eq_1,
  GUT.LiSixQuarkBlockAssembly.entries.eq_1 => Physics.LiSixQuarkBlockAssembly.entries.eq_1,
  GUT.LiSixQuarkBlockExtraction.alternating22_forward => Physics.LiSixQuarkBlockExtraction.alternating22_forward,
  GUT.LiSixQuarkBlockExtraction.decode => Physics.LiSixQuarkBlockExtraction.decode,
  GUT.LiSixQuarkBlockExtraction.decode.eq_1 => Physics.LiSixQuarkBlockExtraction.decode.eq_1,
  GUT.LiSixQuarkBlockExtraction.decodeBlocks => Physics.LiSixQuarkBlockExtraction.decodeBlocks,
  GUT.LiSixQuarkBlockExtraction.decodeBlocks.eq_1 => Physics.LiSixQuarkBlockExtraction.decodeBlocks.eq_1,
  GUT.LiSixQuarkBlockExtraction.decodeLinear => Physics.LiSixQuarkBlockExtraction.decodeLinear,
  GUT.LiSixQuarkBlockExtraction.decode_original => Physics.LiSixQuarkBlockExtraction.decode_original,
  GUT.LiSixQuarkBlockExtraction.decode_presentation => Physics.LiSixQuarkBlockExtraction.decode_presentation,
  GUT.LiSixQuarkBlockExtraction.entriesLinear => Physics.LiSixQuarkBlockExtraction.entriesLinear,
  GUT.LiSixQuarkBlockExtraction.extraction => Physics.LiSixQuarkBlockExtraction.extraction,
  GUT.LiSixQuarkBlockExtraction.pack22 => Physics.LiSixQuarkBlockExtraction.pack22,
  GUT.LiSixQuarkBlockExtraction.pack22.eq_1 => Physics.LiSixQuarkBlockExtraction.pack22.eq_1,
  GUT.LiSixQuarkBlockExtraction.pack22_presentation => Physics.LiSixQuarkBlockExtraction.pack22_presentation,
  GUT.LiSixQuarkBlockExtraction.pack23 => Physics.LiSixQuarkBlockExtraction.pack23,
  GUT.LiSixQuarkBlockExtraction.pack23.eq_1 => Physics.LiSixQuarkBlockExtraction.pack23.eq_1,
  GUT.LiSixQuarkBlockExtraction.pack23_presentation => Physics.LiSixQuarkBlockExtraction.pack23_presentation,
  GUT.LiSixQuarkBlockExtraction.pack32 => Physics.LiSixQuarkBlockExtraction.pack32,
  GUT.LiSixQuarkBlockExtraction.pack32.eq_1 => Physics.LiSixQuarkBlockExtraction.pack32.eq_1,
  GUT.LiSixQuarkBlockExtraction.pack32_presentation => Physics.LiSixQuarkBlockExtraction.pack32_presentation,
  GUT.LiSixQuarkBlockExtraction.pack33 => Physics.LiSixQuarkBlockExtraction.pack33,
  GUT.LiSixQuarkBlockExtraction.pack33.eq_1 => Physics.LiSixQuarkBlockExtraction.pack33.eq_1,
  GUT.LiSixQuarkBlockExtraction.pack33_presentation => Physics.LiSixQuarkBlockExtraction.pack33_presentation,
  GUT.LiSixQuarkBlockExtraction.reindex => Physics.LiSixQuarkBlockExtraction.reindex,
  GUT.LiSixQuarkBlockExtraction.standardFirst22_forward => Physics.LiSixQuarkBlockExtraction.standardFirst22_forward,
  GUT.LiSixQuarkBlockExtraction.standardSecond22_forward => Physics.LiSixQuarkBlockExtraction.standardSecond22_forward,
  GUT.LiSixQuarkBlockExtraction.trace22_forward => Physics.LiSixQuarkBlockExtraction.trace22_forward
]

assert_compatible GUT.LiSixQuarkBlockAssembly.colorEntries.eq_1 => Physics.LiSixQuarkBlockAssembly.colorEntries.eq_1
assert_compatible GUT.LiSixQuarkBlockAssembly.entries.eq_1 => Physics.LiSixQuarkBlockAssembly.entries.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.alternating22_forward => Physics.LiSixQuarkBlockExtraction.alternating22_forward
assert_compatible GUT.LiSixQuarkBlockExtraction.decode => Physics.LiSixQuarkBlockExtraction.decode
assert_compatible GUT.LiSixQuarkBlockExtraction.decode.eq_1 => Physics.LiSixQuarkBlockExtraction.decode.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.decodeBlocks => Physics.LiSixQuarkBlockExtraction.decodeBlocks
assert_compatible GUT.LiSixQuarkBlockExtraction.decodeBlocks.eq_1 => Physics.LiSixQuarkBlockExtraction.decodeBlocks.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.decodeLinear => Physics.LiSixQuarkBlockExtraction.decodeLinear
assert_compatible GUT.LiSixQuarkBlockExtraction.decode_original => Physics.LiSixQuarkBlockExtraction.decode_original
assert_compatible GUT.LiSixQuarkBlockExtraction.decode_presentation => Physics.LiSixQuarkBlockExtraction.decode_presentation
assert_compatible GUT.LiSixQuarkBlockExtraction.entriesLinear => Physics.LiSixQuarkBlockExtraction.entriesLinear
assert_compatible GUT.LiSixQuarkBlockExtraction.extraction => Physics.LiSixQuarkBlockExtraction.extraction
assert_compatible GUT.LiSixQuarkBlockExtraction.pack22 => Physics.LiSixQuarkBlockExtraction.pack22
assert_compatible GUT.LiSixQuarkBlockExtraction.pack22.eq_1 => Physics.LiSixQuarkBlockExtraction.pack22.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.pack22_presentation => Physics.LiSixQuarkBlockExtraction.pack22_presentation
assert_compatible GUT.LiSixQuarkBlockExtraction.pack23 => Physics.LiSixQuarkBlockExtraction.pack23
assert_compatible GUT.LiSixQuarkBlockExtraction.pack23.eq_1 => Physics.LiSixQuarkBlockExtraction.pack23.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.pack23_presentation => Physics.LiSixQuarkBlockExtraction.pack23_presentation
assert_compatible GUT.LiSixQuarkBlockExtraction.pack32 => Physics.LiSixQuarkBlockExtraction.pack32
assert_compatible GUT.LiSixQuarkBlockExtraction.pack32.eq_1 => Physics.LiSixQuarkBlockExtraction.pack32.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.pack32_presentation => Physics.LiSixQuarkBlockExtraction.pack32_presentation
assert_compatible GUT.LiSixQuarkBlockExtraction.pack33 => Physics.LiSixQuarkBlockExtraction.pack33
assert_compatible GUT.LiSixQuarkBlockExtraction.pack33.eq_1 => Physics.LiSixQuarkBlockExtraction.pack33.eq_1
assert_compatible GUT.LiSixQuarkBlockExtraction.pack33_presentation => Physics.LiSixQuarkBlockExtraction.pack33_presentation
assert_compatible GUT.LiSixQuarkBlockExtraction.reindex => Physics.LiSixQuarkBlockExtraction.reindex
assert_compatible GUT.LiSixQuarkBlockExtraction.standardFirst22_forward => Physics.LiSixQuarkBlockExtraction.standardFirst22_forward
assert_compatible GUT.LiSixQuarkBlockExtraction.standardSecond22_forward => Physics.LiSixQuarkBlockExtraction.standardSecond22_forward
assert_compatible GUT.LiSixQuarkBlockExtraction.trace22_forward => Physics.LiSixQuarkBlockExtraction.trace22_forward
