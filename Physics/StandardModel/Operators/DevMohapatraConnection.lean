import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraConnection
import Physics.StandardModel.Operators.DevMohapatraSixQuark
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.SixQuarkConventionalBasis
import Math.RepresentationTheory.SixSlotSpeciesSum
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraConnection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraConnection.F => Physics.DevMohapatraConnection.F,
  GUT.DevMohapatraConnection.FC => Physics.DevMohapatraConnection.FC,
  GUT.DevMohapatraConnection.H => Physics.DevMohapatraConnection.H,
  GUT.DevMohapatraConnection.QF => Physics.DevMohapatraConnection.QF,
  GUT.DevMohapatraConnection.action => Physics.DevMohapatraConnection.action,
  GUT.DevMohapatraConnection.action.eq_1 => Physics.DevMohapatraConnection.action.eq_1,
  GUT.DevMohapatraConnection.downCoupling => Physics.DevMohapatraConnection.downCoupling,
  GUT.DevMohapatraConnection.downCoupling.eq_1 => Physics.DevMohapatraConnection.downCoupling.eq_1,
  GUT.DevMohapatraConnection.downCoupling_same => Physics.DevMohapatraConnection.downCoupling_same,
  GUT.DevMohapatraConnection.downCoupling_selected => Physics.DevMohapatraConnection.downCoupling_selected,
  GUT.DevMohapatraConnection.downCoupling_swap => Physics.DevMohapatraConnection.downCoupling_swap,
  GUT.DevMohapatraConnection.down_action => Physics.DevMohapatraConnection.down_action,
  GUT.DevMohapatraConnection.flavored => Physics.DevMohapatraConnection.flavored,
  GUT.DevMohapatraConnection.flavored_invariant => Physics.DevMohapatraConnection.flavored_invariant,
  GUT.DevMohapatraConnection.flavored_pure => Physics.DevMohapatraConnection.flavored_pure,
  GUT.DevMohapatraConnection.orderedLift => Physics.DevMohapatraConnection.orderedLift,
  GUT.DevMohapatraConnection.orderedLift.eq_1 => Physics.DevMohapatraConnection.orderedLift.eq_1,
  GUT.DevMohapatraConnection.orderedLift_apply => Physics.DevMohapatraConnection.orderedLift_apply,
  GUT.DevMohapatraConnection.physical_invariant => Physics.DevMohapatraConnection.physical_invariant,
  GUT.DevMohapatraConnection.printed => Physics.DevMohapatraConnection.printed,
  GUT.DevMohapatraConnection.printed.eq_1 => Physics.DevMohapatraConnection.printed.eq_1,
  GUT.DevMohapatraConnection.printed_apply => Physics.DevMohapatraConnection.printed_apply,
  GUT.DevMohapatraConnection.printed_evaluation => Physics.DevMohapatraConnection.printed_evaluation,
  GUT.DevMohapatraConnection.printed_invariant => Physics.DevMohapatraConnection.printed_invariant,
  GUT.DevMohapatraConnection.probe => Physics.DevMohapatraConnection.probe,
  GUT.DevMohapatraConnection.project => Physics.DevMohapatraConnection.project,
  GUT.DevMohapatraConnection.project.eq_1 => Physics.DevMohapatraConnection.project.eq_1,
  GUT.DevMohapatraConnection.project_action => Physics.DevMohapatraConnection.project_action,
  GUT.DevMohapatraConnection.project_pure => Physics.DevMohapatraConnection.project_pure,
  GUT.DevMohapatraConnection.residual => Physics.DevMohapatraConnection.residual,
  GUT.DevMohapatraConnection.sourceExterior => Physics.DevMohapatraConnection.sourceExterior,
  GUT.DevMohapatraConnection.sourceExterior_evaluation => Physics.DevMohapatraConnection.sourceExterior_evaluation,
  GUT.DevMohapatraConnection.sourceExterior_invariant => Physics.DevMohapatraConnection.sourceExterior_invariant,
  GUT.DevMohapatraConnection.sourceExterior_nonzero => Physics.DevMohapatraConnection.sourceExterior_nonzero,
  GUT.DevMohapatraConnection.spin => Physics.DevMohapatraConnection.spin,
  GUT.DevMohapatraConnection.spin.eq_1 => Physics.DevMohapatraConnection.spin.eq_1,
  GUT.DevMohapatraConnection.spin_invariant => Physics.DevMohapatraConnection.spin_invariant,
  GUT.DevMohapatraConnection.up_action => Physics.DevMohapatraConnection.up_action,
  GUT.DevMohapatraConnection.weighted_nonzero_iff => Physics.DevMohapatraConnection.weighted_nonzero_iff
]

assert_compatible GUT.DevMohapatraConnection.F => Physics.DevMohapatraConnection.F
assert_compatible GUT.DevMohapatraConnection.FC => Physics.DevMohapatraConnection.FC
assert_compatible GUT.DevMohapatraConnection.H => Physics.DevMohapatraConnection.H
assert_compatible GUT.DevMohapatraConnection.QF => Physics.DevMohapatraConnection.QF
assert_compatible GUT.DevMohapatraConnection.action => Physics.DevMohapatraConnection.action
assert_compatible GUT.DevMohapatraConnection.action.eq_1 => Physics.DevMohapatraConnection.action.eq_1
assert_compatible GUT.DevMohapatraConnection.downCoupling => Physics.DevMohapatraConnection.downCoupling
assert_compatible GUT.DevMohapatraConnection.downCoupling.eq_1 => Physics.DevMohapatraConnection.downCoupling.eq_1
assert_compatible GUT.DevMohapatraConnection.downCoupling_same => Physics.DevMohapatraConnection.downCoupling_same
assert_compatible GUT.DevMohapatraConnection.downCoupling_selected => Physics.DevMohapatraConnection.downCoupling_selected
assert_compatible GUT.DevMohapatraConnection.downCoupling_swap => Physics.DevMohapatraConnection.downCoupling_swap
assert_compatible GUT.DevMohapatraConnection.down_action => Physics.DevMohapatraConnection.down_action
assert_compatible GUT.DevMohapatraConnection.flavored => Physics.DevMohapatraConnection.flavored
assert_compatible GUT.DevMohapatraConnection.flavored_invariant => Physics.DevMohapatraConnection.flavored_invariant
assert_compatible GUT.DevMohapatraConnection.flavored_pure => Physics.DevMohapatraConnection.flavored_pure
assert_compatible GUT.DevMohapatraConnection.orderedLift => Physics.DevMohapatraConnection.orderedLift
assert_compatible GUT.DevMohapatraConnection.orderedLift.eq_1 => Physics.DevMohapatraConnection.orderedLift.eq_1
assert_compatible GUT.DevMohapatraConnection.orderedLift_apply => Physics.DevMohapatraConnection.orderedLift_apply
assert_compatible GUT.DevMohapatraConnection.physical_invariant => Physics.DevMohapatraConnection.physical_invariant
assert_compatible GUT.DevMohapatraConnection.printed => Physics.DevMohapatraConnection.printed
assert_compatible GUT.DevMohapatraConnection.printed.eq_1 => Physics.DevMohapatraConnection.printed.eq_1
assert_compatible GUT.DevMohapatraConnection.printed_apply => Physics.DevMohapatraConnection.printed_apply
assert_compatible GUT.DevMohapatraConnection.printed_evaluation => Physics.DevMohapatraConnection.printed_evaluation
assert_compatible GUT.DevMohapatraConnection.printed_invariant => Physics.DevMohapatraConnection.printed_invariant
assert_compatible GUT.DevMohapatraConnection.probe => Physics.DevMohapatraConnection.probe
assert_compatible GUT.DevMohapatraConnection.project => Physics.DevMohapatraConnection.project
assert_compatible GUT.DevMohapatraConnection.project.eq_1 => Physics.DevMohapatraConnection.project.eq_1
assert_compatible GUT.DevMohapatraConnection.project_action => Physics.DevMohapatraConnection.project_action
assert_compatible GUT.DevMohapatraConnection.project_pure => Physics.DevMohapatraConnection.project_pure
assert_compatible GUT.DevMohapatraConnection.residual => Physics.DevMohapatraConnection.residual
assert_compatible GUT.DevMohapatraConnection.sourceExterior => Physics.DevMohapatraConnection.sourceExterior
assert_compatible GUT.DevMohapatraConnection.sourceExterior_evaluation => Physics.DevMohapatraConnection.sourceExterior_evaluation
assert_compatible GUT.DevMohapatraConnection.sourceExterior_invariant => Physics.DevMohapatraConnection.sourceExterior_invariant
assert_compatible GUT.DevMohapatraConnection.sourceExterior_nonzero => Physics.DevMohapatraConnection.sourceExterior_nonzero
assert_compatible GUT.DevMohapatraConnection.spin => Physics.DevMohapatraConnection.spin
assert_compatible GUT.DevMohapatraConnection.spin.eq_1 => Physics.DevMohapatraConnection.spin.eq_1
assert_compatible GUT.DevMohapatraConnection.spin_invariant => Physics.DevMohapatraConnection.spin_invariant
assert_compatible GUT.DevMohapatraConnection.up_action => Physics.DevMohapatraConnection.up_action
assert_compatible GUT.DevMohapatraConnection.weighted_nonzero_iff => Physics.DevMohapatraConnection.weighted_nonzero_iff
