import Physics.StandardModel.Operators.BaryonOne.Qque.StandardGaugeQqueExterior
import Physics.StandardModel.Operators.PhysicalQqueEndpoint
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.StandardGaugeQqueExterior instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardGaugeQqueExterior.instAddCommGroupQuark => Physics.StandardGaugeQqueExterior.instAddCommGroupQuark,
  GUT.StandardGaugeQqueExterior.internal => Physics.StandardGaugeQqueExterior.internal,
  GUT.StandardGaugeQqueExterior.on_fields => Physics.StandardGaugeQqueExterior.on_fields,
  GUT.StandardGaugeQqueExterior.standard_nonzero => Physics.StandardGaugeQqueExterior.standard_nonzero
]

assert_compatible GUT.StandardGaugeQqueExterior.instAddCommGroupQuark => Physics.StandardGaugeQqueExterior.instAddCommGroupQuark
assert_compatible GUT.StandardGaugeQqueExterior.internal => Physics.StandardGaugeQqueExterior.internal
assert_compatible GUT.StandardGaugeQqueExterior.on_fields => Physics.StandardGaugeQqueExterior.on_fields
assert_compatible GUT.StandardGaugeQqueExterior.standard_nonzero => Physics.StandardGaugeQqueExterior.standard_nonzero
