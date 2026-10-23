import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairSolvers
import Physics.StandardModel.Operators.HeeckLeSixQuarkQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairSolvers instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkPairSolvers.couplingDecode => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode,
  GUT.HeeckLeSixQuarkPairSolvers.couplingDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.couplingDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.couplingDecodeLinear,
  GUT.HeeckLeSixQuarkPairSolvers.couplingDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode_forward,
  GUT.HeeckLeSixQuarkPairSolvers.couplingForward => Physics.HeeckLeSixQuarkPairSolvers.couplingForward,
  GUT.HeeckLeSixQuarkPairSolvers.couplingForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.couplingForward.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.couplingForward_decode => Physics.HeeckLeSixQuarkPairSolvers.couplingForward_decode,
  GUT.HeeckLeSixQuarkPairSolvers.evenDecode => Physics.HeeckLeSixQuarkPairSolvers.evenDecode,
  GUT.HeeckLeSixQuarkPairSolvers.evenDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenDecode.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.evenDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.evenDecodeLinear,
  GUT.HeeckLeSixQuarkPairSolvers.evenDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.evenDecode_forward,
  GUT.HeeckLeSixQuarkPairSolvers.evenForward => Physics.HeeckLeSixQuarkPairSolvers.evenForward,
  GUT.HeeckLeSixQuarkPairSolvers.evenForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenForward.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.evenResidual => Physics.HeeckLeSixQuarkPairSolvers.evenResidual,
  GUT.HeeckLeSixQuarkPairSolvers.evenResidual.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenResidual.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.evenResidualLinear => Physics.HeeckLeSixQuarkPairSolvers.evenResidualLinear,
  GUT.HeeckLeSixQuarkPairSolvers.evenResidual_forward => Physics.HeeckLeSixQuarkPairSolvers.evenResidual_forward,
  GUT.HeeckLeSixQuarkPairSolvers.oddDecode => Physics.HeeckLeSixQuarkPairSolvers.oddDecode,
  GUT.HeeckLeSixQuarkPairSolvers.oddDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddDecode.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.oddDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.oddDecodeLinear,
  GUT.HeeckLeSixQuarkPairSolvers.oddDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.oddDecode_forward,
  GUT.HeeckLeSixQuarkPairSolvers.oddForward => Physics.HeeckLeSixQuarkPairSolvers.oddForward,
  GUT.HeeckLeSixQuarkPairSolvers.oddForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddForward.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.oddResidual => Physics.HeeckLeSixQuarkPairSolvers.oddResidual,
  GUT.HeeckLeSixQuarkPairSolvers.oddResidual.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddResidual.eq_1,
  GUT.HeeckLeSixQuarkPairSolvers.oddResidualLinear => Physics.HeeckLeSixQuarkPairSolvers.oddResidualLinear,
  GUT.HeeckLeSixQuarkPairSolvers.oddResidual_forward => Physics.HeeckLeSixQuarkPairSolvers.oddResidual_forward
]

assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingDecode => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.couplingDecodeLinear
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.couplingDecode_forward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingForward => Physics.HeeckLeSixQuarkPairSolvers.couplingForward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.couplingForward.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.couplingForward_decode => Physics.HeeckLeSixQuarkPairSolvers.couplingForward_decode
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenDecode => Physics.HeeckLeSixQuarkPairSolvers.evenDecode
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenDecode.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.evenDecodeLinear
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.evenDecode_forward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenForward => Physics.HeeckLeSixQuarkPairSolvers.evenForward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenForward.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenResidual => Physics.HeeckLeSixQuarkPairSolvers.evenResidual
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenResidual.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.evenResidual.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenResidualLinear => Physics.HeeckLeSixQuarkPairSolvers.evenResidualLinear
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.evenResidual_forward => Physics.HeeckLeSixQuarkPairSolvers.evenResidual_forward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddDecode => Physics.HeeckLeSixQuarkPairSolvers.oddDecode
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddDecode.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddDecode.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddDecodeLinear => Physics.HeeckLeSixQuarkPairSolvers.oddDecodeLinear
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddDecode_forward => Physics.HeeckLeSixQuarkPairSolvers.oddDecode_forward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddForward => Physics.HeeckLeSixQuarkPairSolvers.oddForward
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddForward.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddForward.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddResidual => Physics.HeeckLeSixQuarkPairSolvers.oddResidual
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddResidual.eq_1 => Physics.HeeckLeSixQuarkPairSolvers.oddResidual.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddResidualLinear => Physics.HeeckLeSixQuarkPairSolvers.oddResidualLinear
assert_compatible GUT.HeeckLeSixQuarkPairSolvers.oddResidual_forward => Physics.HeeckLeSixQuarkPairSolvers.oddResidual_forward
