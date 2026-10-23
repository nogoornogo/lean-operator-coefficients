import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkAssemblyBase
import Physics.StandardModel.Operators.HeeckLeSixQuarkSupport
import Physics.StandardModel.Operators.HeeckLeSixQuarkPairSolvers
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkAssemblyBase instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkAssemblyBase.assemble => Physics.HeeckLeSixQuarkAssemblyBase.assemble,
  GUT.HeeckLeSixQuarkAssemblyBase.assemble.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.assemble.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.assemble_split => Physics.HeeckLeSixQuarkAssemblyBase.assemble_split,
  GUT.HeeckLeSixQuarkAssemblyBase.assemble_weave => Physics.HeeckLeSixQuarkAssemblyBase.assemble_weave,
  GUT.HeeckLeSixQuarkAssemblyBase.combination => Physics.HeeckLeSixQuarkAssemblyBase.combination,
  GUT.HeeckLeSixQuarkAssemblyBase.combination.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.combination.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.even => Physics.HeeckLeSixQuarkAssemblyBase.even,
  GUT.HeeckLeSixQuarkAssemblyBase.odd => Physics.HeeckLeSixQuarkAssemblyBase.odd,
  GUT.HeeckLeSixQuarkAssemblyBase.packResidual => Physics.HeeckLeSixQuarkAssemblyBase.packResidual,
  GUT.HeeckLeSixQuarkAssemblyBase.residual => Physics.HeeckLeSixQuarkAssemblyBase.residual,
  GUT.HeeckLeSixQuarkAssemblyBase.select0 => Physics.HeeckLeSixQuarkAssemblyBase.select0,
  GUT.HeeckLeSixQuarkAssemblyBase.select1 => Physics.HeeckLeSixQuarkAssemblyBase.select1,
  GUT.HeeckLeSixQuarkAssemblyBase.source0Assembly => Physics.HeeckLeSixQuarkAssemblyBase.source0Assembly,
  GUT.HeeckLeSixQuarkAssemblyBase.source0Assembly.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source0Assembly.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.source0Index => Physics.HeeckLeSixQuarkAssemblyBase.source0Index,
  GUT.HeeckLeSixQuarkAssemblyBase.source0Index.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source0Index.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.source0_seed => Physics.HeeckLeSixQuarkAssemblyBase.source0_seed,
  GUT.HeeckLeSixQuarkAssemblyBase.source1Assembly => Physics.HeeckLeSixQuarkAssemblyBase.source1Assembly,
  GUT.HeeckLeSixQuarkAssemblyBase.source1Assembly.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source1Assembly.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.source1Index => Physics.HeeckLeSixQuarkAssemblyBase.source1Index,
  GUT.HeeckLeSixQuarkAssemblyBase.source1Index.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source1Index.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.source1_seed => Physics.HeeckLeSixQuarkAssemblyBase.source1_seed,
  GUT.HeeckLeSixQuarkAssemblyBase.top => Physics.HeeckLeSixQuarkAssemblyBase.top,
  GUT.HeeckLeSixQuarkAssemblyBase.top_pair_zero => Physics.HeeckLeSixQuarkAssemblyBase.top_pair_zero,
  GUT.HeeckLeSixQuarkAssemblyBase.top_source0 => Physics.HeeckLeSixQuarkAssemblyBase.top_source0,
  GUT.HeeckLeSixQuarkAssemblyBase.weave => Physics.HeeckLeSixQuarkAssemblyBase.weave,
  GUT.HeeckLeSixQuarkAssemblyBase.weave.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.weave.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.weaveLinear => Physics.HeeckLeSixQuarkAssemblyBase.weaveLinear,
  GUT.HeeckLeSixQuarkAssemblyBase.weave_select => Physics.HeeckLeSixQuarkAssemblyBase.weave_select
]

assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.assemble => Physics.HeeckLeSixQuarkAssemblyBase.assemble
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.assemble.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.assemble.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.assemble_split => Physics.HeeckLeSixQuarkAssemblyBase.assemble_split
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.assemble_weave => Physics.HeeckLeSixQuarkAssemblyBase.assemble_weave
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.combination => Physics.HeeckLeSixQuarkAssemblyBase.combination
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.combination.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.combination.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.even => Physics.HeeckLeSixQuarkAssemblyBase.even
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.odd => Physics.HeeckLeSixQuarkAssemblyBase.odd
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.packResidual => Physics.HeeckLeSixQuarkAssemblyBase.packResidual
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.residual => Physics.HeeckLeSixQuarkAssemblyBase.residual
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.select0 => Physics.HeeckLeSixQuarkAssemblyBase.select0
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.select1 => Physics.HeeckLeSixQuarkAssemblyBase.select1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source0Assembly => Physics.HeeckLeSixQuarkAssemblyBase.source0Assembly
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source0Assembly.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source0Assembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source0Index => Physics.HeeckLeSixQuarkAssemblyBase.source0Index
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source0Index.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source0Index.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source0_seed => Physics.HeeckLeSixQuarkAssemblyBase.source0_seed
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source1Assembly => Physics.HeeckLeSixQuarkAssemblyBase.source1Assembly
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source1Assembly.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source1Assembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source1Index => Physics.HeeckLeSixQuarkAssemblyBase.source1Index
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source1Index.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.source1Index.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.source1_seed => Physics.HeeckLeSixQuarkAssemblyBase.source1_seed
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.top => Physics.HeeckLeSixQuarkAssemblyBase.top
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.top_pair_zero => Physics.HeeckLeSixQuarkAssemblyBase.top_pair_zero
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.top_source0 => Physics.HeeckLeSixQuarkAssemblyBase.top_source0
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.weave => Physics.HeeckLeSixQuarkAssemblyBase.weave
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.weave.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.weave.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.weaveLinear => Physics.HeeckLeSixQuarkAssemblyBase.weaveLinear
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.weave_select => Physics.HeeckLeSixQuarkAssemblyBase.weave_select
