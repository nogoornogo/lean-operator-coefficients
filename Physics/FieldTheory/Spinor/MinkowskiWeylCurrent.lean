import Physics.FieldTheory.Spinor.Weyl.MinkowskiWeylCurrent
import Physics.FieldTheory.Jets.DerivativeLiteratureMixed
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.MinkowskiWeylCurrent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MinkowskiWeylCurrent.Block => Physics.MinkowskiWeylCurrent.Block,
  GUT.MinkowskiWeylCurrent.anticommuting_reverse => Physics.MinkowskiWeylCurrent.anticommuting_reverse,
  GUT.MinkowskiWeylCurrent.barSigma => Physics.MinkowskiWeylCurrent.barSigma,
  GUT.MinkowskiWeylCurrent.barSigma.eq_1 => Physics.MinkowskiWeylCurrent.barSigma.eq_1,
  GUT.MinkowskiWeylCurrent.barred => Physics.MinkowskiWeylCurrent.barred,
  GUT.MinkowskiWeylCurrent.barred.eq_1 => Physics.MinkowskiWeylCurrent.barred.eq_1,
  GUT.MinkowskiWeylCurrent.clifford => Physics.MinkowskiWeylCurrent.clifford,
  GUT.MinkowskiWeylCurrent.eta => Physics.MinkowskiWeylCurrent.eta,
  GUT.MinkowskiWeylCurrent.eta.eq_1 => Physics.MinkowskiWeylCurrent.eta.eq_1,
  GUT.MinkowskiWeylCurrent.gamma => Physics.MinkowskiWeylCurrent.gamma,
  GUT.MinkowskiWeylCurrent.gamma.eq_1 => Physics.MinkowskiWeylCurrent.gamma.eq_1,
  GUT.MinkowskiWeylCurrent.literal_current => Physics.MinkowskiWeylCurrent.literal_current,
  GUT.MinkowskiWeylCurrent.literal_reversal => Physics.MinkowskiWeylCurrent.literal_reversal,
  GUT.MinkowskiWeylCurrent.ordered => Physics.MinkowskiWeylCurrent.ordered,
  GUT.MinkowskiWeylCurrent.ordered.eq_1 => Physics.MinkowskiWeylCurrent.ordered.eq_1,
  GUT.MinkowskiWeylCurrent.projector => Physics.MinkowskiWeylCurrent.projector,
  GUT.MinkowskiWeylCurrent.projector.eq_1 => Physics.MinkowskiWeylCurrent.projector.eq_1,
  GUT.MinkowskiWeylCurrent.raise => Physics.MinkowskiWeylCurrent.raise,
  GUT.MinkowskiWeylCurrent.raise.eq_1 => Physics.MinkowskiWeylCurrent.raise.eq_1,
  GUT.MinkowskiWeylCurrent.reversedBar => Physics.MinkowskiWeylCurrent.reversedBar,
  GUT.MinkowskiWeylCurrent.reversedBar.eq_1 => Physics.MinkowskiWeylCurrent.reversedBar.eq_1,
  GUT.MinkowskiWeylCurrent.rightBlock => Physics.MinkowskiWeylCurrent.rightBlock,
  GUT.MinkowskiWeylCurrent.rightBlock.eq_1 => Physics.MinkowskiWeylCurrent.rightBlock.eq_1,
  GUT.MinkowskiWeylCurrent.right_block_dictionary => Physics.MinkowskiWeylCurrent.right_block_dictionary,
  GUT.MinkowskiWeylCurrent.right_projector => Physics.MinkowskiWeylCurrent.right_projector,
  GUT.MinkowskiWeylCurrent.sigma => Physics.MinkowskiWeylCurrent.sigma,
  GUT.MinkowskiWeylCurrent.spinor => Physics.MinkowskiWeylCurrent.spinor,
  GUT.MinkowskiWeylCurrent.spinor.eq_1 => Physics.MinkowskiWeylCurrent.spinor.eq_1
]

assert_compatible GUT.MinkowskiWeylCurrent.Block => Physics.MinkowskiWeylCurrent.Block
assert_compatible GUT.MinkowskiWeylCurrent.anticommuting_reverse => Physics.MinkowskiWeylCurrent.anticommuting_reverse
assert_compatible GUT.MinkowskiWeylCurrent.barSigma => Physics.MinkowskiWeylCurrent.barSigma
assert_compatible GUT.MinkowskiWeylCurrent.barSigma.eq_1 => Physics.MinkowskiWeylCurrent.barSigma.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.barred => Physics.MinkowskiWeylCurrent.barred
assert_compatible GUT.MinkowskiWeylCurrent.barred.eq_1 => Physics.MinkowskiWeylCurrent.barred.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.clifford => Physics.MinkowskiWeylCurrent.clifford
assert_compatible GUT.MinkowskiWeylCurrent.eta => Physics.MinkowskiWeylCurrent.eta
assert_compatible GUT.MinkowskiWeylCurrent.eta.eq_1 => Physics.MinkowskiWeylCurrent.eta.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.gamma => Physics.MinkowskiWeylCurrent.gamma
assert_compatible GUT.MinkowskiWeylCurrent.gamma.eq_1 => Physics.MinkowskiWeylCurrent.gamma.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.literal_current => Physics.MinkowskiWeylCurrent.literal_current
assert_compatible GUT.MinkowskiWeylCurrent.literal_reversal => Physics.MinkowskiWeylCurrent.literal_reversal
assert_compatible GUT.MinkowskiWeylCurrent.ordered => Physics.MinkowskiWeylCurrent.ordered
assert_compatible GUT.MinkowskiWeylCurrent.ordered.eq_1 => Physics.MinkowskiWeylCurrent.ordered.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.projector => Physics.MinkowskiWeylCurrent.projector
assert_compatible GUT.MinkowskiWeylCurrent.projector.eq_1 => Physics.MinkowskiWeylCurrent.projector.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.raise => Physics.MinkowskiWeylCurrent.raise
assert_compatible GUT.MinkowskiWeylCurrent.raise.eq_1 => Physics.MinkowskiWeylCurrent.raise.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.reversedBar => Physics.MinkowskiWeylCurrent.reversedBar
assert_compatible GUT.MinkowskiWeylCurrent.reversedBar.eq_1 => Physics.MinkowskiWeylCurrent.reversedBar.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.rightBlock => Physics.MinkowskiWeylCurrent.rightBlock
assert_compatible GUT.MinkowskiWeylCurrent.rightBlock.eq_1 => Physics.MinkowskiWeylCurrent.rightBlock.eq_1
assert_compatible GUT.MinkowskiWeylCurrent.right_block_dictionary => Physics.MinkowskiWeylCurrent.right_block_dictionary
assert_compatible GUT.MinkowskiWeylCurrent.right_projector => Physics.MinkowskiWeylCurrent.right_projector
assert_compatible GUT.MinkowskiWeylCurrent.sigma => Physics.MinkowskiWeylCurrent.sigma
assert_compatible GUT.MinkowskiWeylCurrent.spinor => Physics.MinkowskiWeylCurrent.spinor
assert_compatible GUT.MinkowskiWeylCurrent.spinor.eq_1 => Physics.MinkowskiWeylCurrent.spinor.eq_1
