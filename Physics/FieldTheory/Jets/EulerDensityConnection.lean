import Physics.FieldTheory.Jets.Lagrangian.EulerDensityConnection
import Math.RepresentationTheory.StandardDensityAction
import Physics.FieldTheory.Jets.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.LagrangianModelLiterature
import Physics.FieldTheory.Jets.YukawaModelControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.EulerDensityConnection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.EulerDensityConnection.Group => Physics.EulerDensityConnection.Group,
  GUT.EulerDensityConnection.automaticModel => Physics.EulerDensityConnection.automaticModel,
  GUT.EulerDensityConnection.automatic_euler => Physics.EulerDensityConnection.automatic_euler,
  GUT.EulerDensityConnection.broken_density_rejected => Physics.EulerDensityConnection.broken_density_rejected,
  GUT.EulerDensityConnection.densityAdd => Physics.EulerDensityConnection.densityAdd,
  GUT.EulerDensityConnection.densityModule => Physics.EulerDensityConnection.densityModule,
  GUT.EulerDensityConnection.densityRing => Physics.EulerDensityConnection.densityRing,
  GUT.EulerDensityConnection.model_eq => Physics.EulerDensityConnection.model_eq,
  GUT.EulerDensityConnection.paper_euler => Physics.EulerDensityConnection.paper_euler
]

assert_compatible GUT.EulerDensityConnection.Group => Physics.EulerDensityConnection.Group
assert_compatible GUT.EulerDensityConnection.automaticModel => Physics.EulerDensityConnection.automaticModel
assert_compatible GUT.EulerDensityConnection.automatic_euler => Physics.EulerDensityConnection.automatic_euler
assert_compatible GUT.EulerDensityConnection.broken_density_rejected => Physics.EulerDensityConnection.broken_density_rejected
assert_compatible GUT.EulerDensityConnection.densityAdd => Physics.EulerDensityConnection.densityAdd
assert_compatible GUT.EulerDensityConnection.densityModule => Physics.EulerDensityConnection.densityModule
assert_compatible GUT.EulerDensityConnection.densityRing => Physics.EulerDensityConnection.densityRing
assert_compatible GUT.EulerDensityConnection.model_eq => Physics.EulerDensityConnection.model_eq
assert_compatible GUT.EulerDensityConnection.paper_euler => Physics.EulerDensityConnection.paper_euler
