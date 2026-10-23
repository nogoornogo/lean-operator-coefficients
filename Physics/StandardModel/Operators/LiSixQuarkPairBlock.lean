import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPairBlock
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPairBlock instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkPairBlock.LocalArray => Physics.LiSixQuarkPairBlock.LocalArray,
  GUT.LiSixQuarkPairBlock.alternatingCoefficient => Physics.LiSixQuarkPairBlock.alternatingCoefficient,
  GUT.LiSixQuarkPairBlock.alternatingCoefficient.eq_1 => Physics.LiSixQuarkPairBlock.alternatingCoefficient.eq_1,
  GUT.LiSixQuarkPairBlock.alternatingSeed => Physics.LiSixQuarkPairBlock.alternatingSeed,
  GUT.LiSixQuarkPairBlock.alternatingSeed.eq_1 => Physics.LiSixQuarkPairBlock.alternatingSeed.eq_1,
  GUT.LiSixQuarkPairBlock.encode => Physics.LiSixQuarkPairBlock.encode,
  GUT.LiSixQuarkPairBlock.encode.eq_1 => Physics.LiSixQuarkPairBlock.encode.eq_1,
  GUT.LiSixQuarkPairBlock.encode_zero_iff => Physics.LiSixQuarkPairBlock.encode_zero_iff,
  GUT.LiSixQuarkPairBlock.exchangedSeed => Physics.LiSixQuarkPairBlock.exchangedSeed,
  GUT.LiSixQuarkPairBlock.exchangedSeed.eq_1 => Physics.LiSixQuarkPairBlock.exchangedSeed.eq_1,
  GUT.LiSixQuarkPairBlock.kernel_reconstruction => Physics.LiSixQuarkPairBlock.kernel_reconstruction,
  GUT.LiSixQuarkPairBlock.probe_encode => Physics.LiSixQuarkPairBlock.probe_encode,
  GUT.LiSixQuarkPairBlock.reconstruction => Physics.LiSixQuarkPairBlock.reconstruction,
  GUT.LiSixQuarkPairBlock.standardFirst => Physics.LiSixQuarkPairBlock.standardFirst,
  GUT.LiSixQuarkPairBlock.standardFirst.eq_1 => Physics.LiSixQuarkPairBlock.standardFirst.eq_1,
  GUT.LiSixQuarkPairBlock.standardSecond => Physics.LiSixQuarkPairBlock.standardSecond,
  GUT.LiSixQuarkPairBlock.standardSecond.eq_1 => Physics.LiSixQuarkPairBlock.standardSecond.eq_1,
  GUT.LiSixQuarkPairBlock.standardSeed => Physics.LiSixQuarkPairBlock.standardSeed,
  GUT.LiSixQuarkPairBlock.standardSeed.eq_1 => Physics.LiSixQuarkPairBlock.standardSeed.eq_1,
  GUT.LiSixQuarkPairBlock.traceCoefficient => Physics.LiSixQuarkPairBlock.traceCoefficient,
  GUT.LiSixQuarkPairBlock.traceCoefficient.eq_1 => Physics.LiSixQuarkPairBlock.traceCoefficient.eq_1
]

assert_compatible GUT.LiSixQuarkPairBlock.LocalArray => Physics.LiSixQuarkPairBlock.LocalArray
assert_compatible GUT.LiSixQuarkPairBlock.alternatingCoefficient => Physics.LiSixQuarkPairBlock.alternatingCoefficient
assert_compatible GUT.LiSixQuarkPairBlock.alternatingCoefficient.eq_1 => Physics.LiSixQuarkPairBlock.alternatingCoefficient.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.alternatingSeed => Physics.LiSixQuarkPairBlock.alternatingSeed
assert_compatible GUT.LiSixQuarkPairBlock.alternatingSeed.eq_1 => Physics.LiSixQuarkPairBlock.alternatingSeed.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.encode => Physics.LiSixQuarkPairBlock.encode
assert_compatible GUT.LiSixQuarkPairBlock.encode.eq_1 => Physics.LiSixQuarkPairBlock.encode.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.encode_zero_iff => Physics.LiSixQuarkPairBlock.encode_zero_iff
assert_compatible GUT.LiSixQuarkPairBlock.exchangedSeed => Physics.LiSixQuarkPairBlock.exchangedSeed
assert_compatible GUT.LiSixQuarkPairBlock.exchangedSeed.eq_1 => Physics.LiSixQuarkPairBlock.exchangedSeed.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.kernel_reconstruction => Physics.LiSixQuarkPairBlock.kernel_reconstruction
assert_compatible GUT.LiSixQuarkPairBlock.probe_encode => Physics.LiSixQuarkPairBlock.probe_encode
assert_compatible GUT.LiSixQuarkPairBlock.reconstruction => Physics.LiSixQuarkPairBlock.reconstruction
assert_compatible GUT.LiSixQuarkPairBlock.standardFirst => Physics.LiSixQuarkPairBlock.standardFirst
assert_compatible GUT.LiSixQuarkPairBlock.standardFirst.eq_1 => Physics.LiSixQuarkPairBlock.standardFirst.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.standardSecond => Physics.LiSixQuarkPairBlock.standardSecond
assert_compatible GUT.LiSixQuarkPairBlock.standardSecond.eq_1 => Physics.LiSixQuarkPairBlock.standardSecond.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.standardSeed => Physics.LiSixQuarkPairBlock.standardSeed
assert_compatible GUT.LiSixQuarkPairBlock.standardSeed.eq_1 => Physics.LiSixQuarkPairBlock.standardSeed.eq_1
assert_compatible GUT.LiSixQuarkPairBlock.traceCoefficient => Physics.LiSixQuarkPairBlock.traceCoefficient
assert_compatible GUT.LiSixQuarkPairBlock.traceCoefficient.eq_1 => Physics.LiSixQuarkPairBlock.traceCoefficient.eq_1
