import Physics.StandardModel.Operators.BaryonOne.Qque.PhysicalQqueEndpoint
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.PhysicalQqueEndpoint instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PhysicalQqueEndpoint.HasExterior => Physics.PhysicalQqueEndpoint.HasExterior,
  GUT.PhysicalQqueEndpoint.of_alternation => Physics.PhysicalQqueEndpoint.of_alternation,
  GUT.PhysicalQqueEndpoint.of_exists => Physics.PhysicalQqueEndpoint.of_exists
]

assert_compatible GUT.PhysicalQqueEndpoint.HasExterior => Physics.PhysicalQqueEndpoint.HasExterior
assert_compatible GUT.PhysicalQqueEndpoint.of_alternation => Physics.PhysicalQqueEndpoint.of_alternation
assert_compatible GUT.PhysicalQqueEndpoint.of_exists => Physics.PhysicalQqueEndpoint.of_exists
