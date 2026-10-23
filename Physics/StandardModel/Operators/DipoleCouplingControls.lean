import Physics.StandardModel.Operators.Dipole.DipoleCouplingControls
import Physics.StandardModel.Operators.DipoleCouplingModel
import Physics.StandardModel.Operators.DipoleControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleCouplingControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleCouplingControls.model => Physics.DipoleCouplingControls.model,
  GUT.DipoleCouplingControls.model.eq_1 => Physics.DipoleCouplingControls.model.eq_1,
  GUT.DipoleCouplingControls.nonlinear_pullback => Physics.DipoleCouplingControls.nonlinear_pullback,
  GUT.DipoleCouplingControls.nonzero_iff => Physics.DipoleCouplingControls.nonzero_iff,
  GUT.DipoleCouplingControls.selected => Physics.DipoleCouplingControls.selected,
  GUT.DipoleCouplingControls.zero_propagator => Physics.DipoleCouplingControls.zero_propagator
]

assert_compatible GUT.DipoleCouplingControls.model => Physics.DipoleCouplingControls.model
assert_compatible GUT.DipoleCouplingControls.model.eq_1 => Physics.DipoleCouplingControls.model.eq_1
assert_compatible GUT.DipoleCouplingControls.nonlinear_pullback => Physics.DipoleCouplingControls.nonlinear_pullback
assert_compatible GUT.DipoleCouplingControls.nonzero_iff => Physics.DipoleCouplingControls.nonzero_iff
assert_compatible GUT.DipoleCouplingControls.selected => Physics.DipoleCouplingControls.selected
assert_compatible GUT.DipoleCouplingControls.zero_propagator => Physics.DipoleCouplingControls.zero_propagator
