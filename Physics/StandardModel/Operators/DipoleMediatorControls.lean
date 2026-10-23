import Physics.StandardModel.Operators.Dipole.DipoleMediatorControls
import Physics.StandardModel.Operators.DipoleMediatorPaths
import Physics.StandardModel.Operators.DipoleControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleMediatorControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleMediatorControls.cancellation => Physics.DipoleMediatorControls.cancellation,
  GUT.DipoleMediatorControls.each_path_nonzero => Physics.DipoleMediatorControls.each_path_nonzero,
  GUT.DipoleMediatorControls.generation => Physics.DipoleMediatorControls.generation,
  GUT.DipoleMediatorControls.generation.eq_1 => Physics.DipoleMediatorControls.generation.eq_1,
  GUT.DipoleMediatorControls.incoming => Physics.DipoleMediatorControls.incoming,
  GUT.DipoleMediatorControls.incoming.eq_1 => Physics.DipoleMediatorControls.incoming.eq_1,
  GUT.DipoleMediatorControls.nonzero_iff => Physics.DipoleMediatorControls.nonzero_iff,
  GUT.DipoleMediatorControls.outgoing => Physics.DipoleMediatorControls.outgoing,
  GUT.DipoleMediatorControls.outgoing.eq_1 => Physics.DipoleMediatorControls.outgoing.eq_1,
  GUT.DipoleMediatorControls.realized => Physics.DipoleMediatorControls.realized,
  GUT.DipoleMediatorControls.restricted_family_vanishes => Physics.DipoleMediatorControls.restricted_family_vanishes,
  GUT.DipoleMediatorControls.selected => Physics.DipoleMediatorControls.selected,
  GUT.DipoleMediatorControls.weakOutgoing => Physics.DipoleMediatorControls.weakOutgoing,
  GUT.DipoleMediatorControls.weakOutgoing.eq_1 => Physics.DipoleMediatorControls.weakOutgoing.eq_1,
  GUT.DipoleMediatorControls.weights => Physics.DipoleMediatorControls.weights,
  GUT.DipoleMediatorControls.weights.eq_1 => Physics.DipoleMediatorControls.weights.eq_1,
  GUT.DipoleMediatorControls.weights_isolate => Physics.DipoleMediatorControls.weights_isolate
]

assert_compatible GUT.DipoleMediatorControls.cancellation => Physics.DipoleMediatorControls.cancellation
assert_compatible GUT.DipoleMediatorControls.each_path_nonzero => Physics.DipoleMediatorControls.each_path_nonzero
assert_compatible GUT.DipoleMediatorControls.generation => Physics.DipoleMediatorControls.generation
assert_compatible GUT.DipoleMediatorControls.generation.eq_1 => Physics.DipoleMediatorControls.generation.eq_1
assert_compatible GUT.DipoleMediatorControls.incoming => Physics.DipoleMediatorControls.incoming
assert_compatible GUT.DipoleMediatorControls.incoming.eq_1 => Physics.DipoleMediatorControls.incoming.eq_1
assert_compatible GUT.DipoleMediatorControls.nonzero_iff => Physics.DipoleMediatorControls.nonzero_iff
assert_compatible GUT.DipoleMediatorControls.outgoing => Physics.DipoleMediatorControls.outgoing
assert_compatible GUT.DipoleMediatorControls.outgoing.eq_1 => Physics.DipoleMediatorControls.outgoing.eq_1
assert_compatible GUT.DipoleMediatorControls.realized => Physics.DipoleMediatorControls.realized
assert_compatible GUT.DipoleMediatorControls.restricted_family_vanishes => Physics.DipoleMediatorControls.restricted_family_vanishes
assert_compatible GUT.DipoleMediatorControls.selected => Physics.DipoleMediatorControls.selected
assert_compatible GUT.DipoleMediatorControls.weakOutgoing => Physics.DipoleMediatorControls.weakOutgoing
assert_compatible GUT.DipoleMediatorControls.weakOutgoing.eq_1 => Physics.DipoleMediatorControls.weakOutgoing.eq_1
assert_compatible GUT.DipoleMediatorControls.weights => Physics.DipoleMediatorControls.weights
assert_compatible GUT.DipoleMediatorControls.weights.eq_1 => Physics.DipoleMediatorControls.weights.eq_1
assert_compatible GUT.DipoleMediatorControls.weights_isolate => Physics.DipoleMediatorControls.weights_isolate
