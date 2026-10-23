import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedSeeds
import Physics.StandardModel.Operators.LiSixQuarkYoungImages
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkReducedSeeds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkLocalAction.column.eq_1 => Physics.LiSixQuarkLocalAction.column.eq_1,
  GUT.LiSixQuarkLocalAction.row.eq_1 => Physics.LiSixQuarkLocalAction.row.eq_1,
  GUT.LiSixQuarkReducedAction.extractColor.eq_1 => Physics.LiSixQuarkReducedAction.extractColor.eq_1,
  GUT.LiSixQuarkReducedAction.extractSpin.eq_1 => Physics.LiSixQuarkReducedAction.extractSpin.eq_1,
  GUT.LiSixQuarkReducedAction.extraction.eq_1 => Physics.LiSixQuarkReducedAction.extraction.eq_1,
  GUT.LiSixQuarkReducedSeeds.extra_seed => Physics.LiSixQuarkReducedSeeds.extra_seed,
  GUT.LiSixQuarkReducedSeeds.extraction_projected => Physics.LiSixQuarkReducedSeeds.extraction_projected,
  GUT.LiSixQuarkReducedSeeds.extraction_raw => Physics.LiSixQuarkReducedSeeds.extraction_raw,
  GUT.LiSixQuarkReducedSeeds.image => Physics.LiSixQuarkReducedSeeds.image,
  GUT.LiSixQuarkReducedSeeds.printed_probe_zero => Physics.LiSixQuarkReducedSeeds.printed_probe_zero,
  GUT.LiSixQuarkReducedSeeds.printed_trace_zero => Physics.LiSixQuarkReducedSeeds.printed_trace_zero,
  GUT.LiSixQuarkReducedSeeds.probe_eq_trace => Physics.LiSixQuarkReducedSeeds.probe_eq_trace,
  GUT.LiSixQuarkReducedSeeds.reducedImage => Physics.LiSixQuarkReducedSeeds.reducedImage,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_1,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_10 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_10,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_11 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_11,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_2 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_2,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_3 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_3,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_4 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_4,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_5 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_5,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_6 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_6,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_7 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_7,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_8 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_8,
  GUT.LiSixQuarkReducedSeeds.reducedImage.eq_9 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_9,
  GUT.LiSixQuarkReducedSeeds.reducedRaw => Physics.LiSixQuarkReducedSeeds.reducedRaw,
  GUT.LiSixQuarkReducedSeeds.reducedRaw.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedRaw.eq_1,
  GUT.LiSixQuarkReducedSeeds.reducedSeed => Physics.LiSixQuarkReducedSeeds.reducedSeed,
  GUT.LiSixQuarkReducedSeeds.reducedSeed.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedSeed.eq_1
]

assert_compatible GUT.LiSixQuarkLocalAction.column.eq_1 => Physics.LiSixQuarkLocalAction.column.eq_1
assert_compatible GUT.LiSixQuarkLocalAction.row.eq_1 => Physics.LiSixQuarkLocalAction.row.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.extractColor.eq_1 => Physics.LiSixQuarkReducedAction.extractColor.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.extractSpin.eq_1 => Physics.LiSixQuarkReducedAction.extractSpin.eq_1
assert_compatible GUT.LiSixQuarkReducedAction.extraction.eq_1 => Physics.LiSixQuarkReducedAction.extraction.eq_1
assert_compatible GUT.LiSixQuarkReducedSeeds.extra_seed => Physics.LiSixQuarkReducedSeeds.extra_seed
assert_compatible GUT.LiSixQuarkReducedSeeds.extraction_projected => Physics.LiSixQuarkReducedSeeds.extraction_projected
assert_compatible GUT.LiSixQuarkReducedSeeds.extraction_raw => Physics.LiSixQuarkReducedSeeds.extraction_raw
assert_compatible GUT.LiSixQuarkReducedSeeds.image => Physics.LiSixQuarkReducedSeeds.image
assert_compatible GUT.LiSixQuarkReducedSeeds.printed_probe_zero => Physics.LiSixQuarkReducedSeeds.printed_probe_zero
assert_compatible GUT.LiSixQuarkReducedSeeds.printed_trace_zero => Physics.LiSixQuarkReducedSeeds.printed_trace_zero
assert_compatible GUT.LiSixQuarkReducedSeeds.probe_eq_trace => Physics.LiSixQuarkReducedSeeds.probe_eq_trace
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage => Physics.LiSixQuarkReducedSeeds.reducedImage
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_1
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_10 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_10
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_11 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_11
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_2 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_2
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_3 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_3
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_4 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_4
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_5 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_5
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_6 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_6
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_7 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_7
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_8 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_8
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedImage.eq_9 => Physics.LiSixQuarkReducedSeeds.reducedImage.eq_9
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedRaw => Physics.LiSixQuarkReducedSeeds.reducedRaw
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedRaw.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedRaw.eq_1
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedSeed => Physics.LiSixQuarkReducedSeeds.reducedSeed
assert_compatible GUT.LiSixQuarkReducedSeeds.reducedSeed.eq_1 => Physics.LiSixQuarkReducedSeeds.reducedSeed.eq_1
