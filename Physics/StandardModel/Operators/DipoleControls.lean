import Physics.StandardModel.Operators.Dipole.DipoleControls
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleControls.Flavor => Physics.DipoleControls.Flavor,
  GUT.DipoleControls.allowed_not_realized_by_zero => Physics.DipoleControls.allowed_not_realized_by_zero,
  GUT.DipoleControls.bridge => Physics.DipoleControls.bridge,
  GUT.DipoleControls.bridge.eq_1 => Physics.DipoleControls.bridge.eq_1,
  GUT.DipoleControls.bridge_selected => Physics.DipoleControls.bridge_selected,
  GUT.DipoleControls.diagonal_selected => Physics.DipoleControls.diagonal_selected,
  GUT.DipoleControls.electron => Physics.DipoleControls.electron,
  GUT.DipoleControls.electron.eq_1 => Physics.DipoleControls.electron.eq_1,
  GUT.DipoleControls.flavor => Physics.DipoleControls.flavor,
  GUT.DipoleControls.generation => Physics.DipoleControls.generation,
  GUT.DipoleControls.generation_nonzero_iff => Physics.DipoleControls.generation_nonzero_iff,
  GUT.DipoleControls.generation_not_additive => Physics.DipoleControls.generation_not_additive,
  GUT.DipoleControls.generation_selected => Physics.DipoleControls.generation_selected,
  GUT.DipoleControls.mu => Physics.DipoleControls.mu,
  GUT.DipoleControls.mu.eq_1 => Physics.DipoleControls.mu.eq_1
]

assert_compatible GUT.DipoleControls.Flavor => Physics.DipoleControls.Flavor
assert_compatible GUT.DipoleControls.allowed_not_realized_by_zero => Physics.DipoleControls.allowed_not_realized_by_zero
assert_compatible GUT.DipoleControls.bridge => Physics.DipoleControls.bridge
assert_compatible GUT.DipoleControls.bridge.eq_1 => Physics.DipoleControls.bridge.eq_1
assert_compatible GUT.DipoleControls.bridge_selected => Physics.DipoleControls.bridge_selected
assert_compatible GUT.DipoleControls.diagonal_selected => Physics.DipoleControls.diagonal_selected
assert_compatible GUT.DipoleControls.electron => Physics.DipoleControls.electron
assert_compatible GUT.DipoleControls.electron.eq_1 => Physics.DipoleControls.electron.eq_1
assert_compatible GUT.DipoleControls.flavor => Physics.DipoleControls.flavor
assert_compatible GUT.DipoleControls.generation => Physics.DipoleControls.generation
assert_compatible GUT.DipoleControls.generation_nonzero_iff => Physics.DipoleControls.generation_nonzero_iff
assert_compatible GUT.DipoleControls.generation_not_additive => Physics.DipoleControls.generation_not_additive
assert_compatible GUT.DipoleControls.generation_selected => Physics.DipoleControls.generation_selected
assert_compatible GUT.DipoleControls.mu => Physics.DipoleControls.mu
assert_compatible GUT.DipoleControls.mu.eq_1 => Physics.DipoleControls.mu.eq_1
