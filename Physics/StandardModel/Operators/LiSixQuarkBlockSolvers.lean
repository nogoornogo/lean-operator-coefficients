import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockSolvers
import Physics.StandardModel.Operators.LiSixQuarkPairBlock
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockSolvers instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkBlockSolvers.difference32 => Physics.LiSixQuarkBlockSolvers.difference32,
  GUT.LiSixQuarkBlockSolvers.difference32.eq_1 => Physics.LiSixQuarkBlockSolvers.difference32.eq_1,
  GUT.LiSixQuarkBlockSolvers.difference32_forward => Physics.LiSixQuarkBlockSolvers.difference32_forward,
  GUT.LiSixQuarkBlockSolvers.first23 => Physics.LiSixQuarkBlockSolvers.first23,
  GUT.LiSixQuarkBlockSolvers.first23.eq_1 => Physics.LiSixQuarkBlockSolvers.first23.eq_1,
  GUT.LiSixQuarkBlockSolvers.first23_forward => Physics.LiSixQuarkBlockSolvers.first23_forward,
  GUT.LiSixQuarkBlockSolvers.first32 => Physics.LiSixQuarkBlockSolvers.first32,
  GUT.LiSixQuarkBlockSolvers.first32.eq_1 => Physics.LiSixQuarkBlockSolvers.first32.eq_1,
  GUT.LiSixQuarkBlockSolvers.first32_forward => Physics.LiSixQuarkBlockSolvers.first32_forward,
  GUT.LiSixQuarkBlockSolvers.first33 => Physics.LiSixQuarkBlockSolvers.first33,
  GUT.LiSixQuarkBlockSolvers.first33.eq_1 => Physics.LiSixQuarkBlockSolvers.first33.eq_1,
  GUT.LiSixQuarkBlockSolvers.first33_forward => Physics.LiSixQuarkBlockSolvers.first33_forward,
  GUT.LiSixQuarkBlockSolvers.forward23 => Physics.LiSixQuarkBlockSolvers.forward23,
  GUT.LiSixQuarkBlockSolvers.forward23.eq_1 => Physics.LiSixQuarkBlockSolvers.forward23.eq_1,
  GUT.LiSixQuarkBlockSolvers.forward32 => Physics.LiSixQuarkBlockSolvers.forward32,
  GUT.LiSixQuarkBlockSolvers.forward32.eq_1 => Physics.LiSixQuarkBlockSolvers.forward32.eq_1,
  GUT.LiSixQuarkBlockSolvers.forward33 => Physics.LiSixQuarkBlockSolvers.forward33,
  GUT.LiSixQuarkBlockSolvers.forward33.eq_1 => Physics.LiSixQuarkBlockSolvers.forward33.eq_1,
  GUT.LiSixQuarkBlockSolvers.last33 => Physics.LiSixQuarkBlockSolvers.last33,
  GUT.LiSixQuarkBlockSolvers.last33.eq_1 => Physics.LiSixQuarkBlockSolvers.last33.eq_1,
  GUT.LiSixQuarkBlockSolvers.last33_forward => Physics.LiSixQuarkBlockSolvers.last33_forward,
  GUT.LiSixQuarkBlockSolvers.pair33 => Physics.LiSixQuarkBlockSolvers.pair33,
  GUT.LiSixQuarkBlockSolvers.pair33.eq_1 => Physics.LiSixQuarkBlockSolvers.pair33.eq_1,
  GUT.LiSixQuarkBlockSolvers.pair33_forward => Physics.LiSixQuarkBlockSolvers.pair33_forward,
  GUT.LiSixQuarkBlockSolvers.scalar33 => Physics.LiSixQuarkBlockSolvers.scalar33,
  GUT.LiSixQuarkBlockSolvers.scalar33.eq_1 => Physics.LiSixQuarkBlockSolvers.scalar33.eq_1,
  GUT.LiSixQuarkBlockSolvers.scalar33_forward => Physics.LiSixQuarkBlockSolvers.scalar33_forward,
  GUT.LiSixQuarkBlockSolvers.sum23 => Physics.LiSixQuarkBlockSolvers.sum23,
  GUT.LiSixQuarkBlockSolvers.sum23.eq_1 => Physics.LiSixQuarkBlockSolvers.sum23.eq_1,
  GUT.LiSixQuarkBlockSolvers.sum23_forward => Physics.LiSixQuarkBlockSolvers.sum23_forward
]

assert_compatible GUT.LiSixQuarkBlockSolvers.difference32 => Physics.LiSixQuarkBlockSolvers.difference32
assert_compatible GUT.LiSixQuarkBlockSolvers.difference32.eq_1 => Physics.LiSixQuarkBlockSolvers.difference32.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.difference32_forward => Physics.LiSixQuarkBlockSolvers.difference32_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.first23 => Physics.LiSixQuarkBlockSolvers.first23
assert_compatible GUT.LiSixQuarkBlockSolvers.first23.eq_1 => Physics.LiSixQuarkBlockSolvers.first23.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.first23_forward => Physics.LiSixQuarkBlockSolvers.first23_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.first32 => Physics.LiSixQuarkBlockSolvers.first32
assert_compatible GUT.LiSixQuarkBlockSolvers.first32.eq_1 => Physics.LiSixQuarkBlockSolvers.first32.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.first32_forward => Physics.LiSixQuarkBlockSolvers.first32_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.first33 => Physics.LiSixQuarkBlockSolvers.first33
assert_compatible GUT.LiSixQuarkBlockSolvers.first33.eq_1 => Physics.LiSixQuarkBlockSolvers.first33.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.first33_forward => Physics.LiSixQuarkBlockSolvers.first33_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.forward23 => Physics.LiSixQuarkBlockSolvers.forward23
assert_compatible GUT.LiSixQuarkBlockSolvers.forward23.eq_1 => Physics.LiSixQuarkBlockSolvers.forward23.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.forward32 => Physics.LiSixQuarkBlockSolvers.forward32
assert_compatible GUT.LiSixQuarkBlockSolvers.forward32.eq_1 => Physics.LiSixQuarkBlockSolvers.forward32.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.forward33 => Physics.LiSixQuarkBlockSolvers.forward33
assert_compatible GUT.LiSixQuarkBlockSolvers.forward33.eq_1 => Physics.LiSixQuarkBlockSolvers.forward33.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.last33 => Physics.LiSixQuarkBlockSolvers.last33
assert_compatible GUT.LiSixQuarkBlockSolvers.last33.eq_1 => Physics.LiSixQuarkBlockSolvers.last33.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.last33_forward => Physics.LiSixQuarkBlockSolvers.last33_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.pair33 => Physics.LiSixQuarkBlockSolvers.pair33
assert_compatible GUT.LiSixQuarkBlockSolvers.pair33.eq_1 => Physics.LiSixQuarkBlockSolvers.pair33.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.pair33_forward => Physics.LiSixQuarkBlockSolvers.pair33_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.scalar33 => Physics.LiSixQuarkBlockSolvers.scalar33
assert_compatible GUT.LiSixQuarkBlockSolvers.scalar33.eq_1 => Physics.LiSixQuarkBlockSolvers.scalar33.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.scalar33_forward => Physics.LiSixQuarkBlockSolvers.scalar33_forward
assert_compatible GUT.LiSixQuarkBlockSolvers.sum23 => Physics.LiSixQuarkBlockSolvers.sum23
assert_compatible GUT.LiSixQuarkBlockSolvers.sum23.eq_1 => Physics.LiSixQuarkBlockSolvers.sum23.eq_1
assert_compatible GUT.LiSixQuarkBlockSolvers.sum23_forward => Physics.LiSixQuarkBlockSolvers.sum23_forward
