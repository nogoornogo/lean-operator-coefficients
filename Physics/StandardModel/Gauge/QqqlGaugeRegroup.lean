import Physics.StandardModel.Gauge.Tensors.QqqlGaugeRegroup
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.QqqlGaugeRegroup instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlGaugeRegroup.equiv => Physics.QqqlGaugeRegroup.equiv,
  GUT.QqqlGaugeRegroup.linearEquiv => Physics.QqqlGaugeRegroup.linearEquiv,
  GUT.QqqlGaugeRegroup.linearEquiv_apply => Physics.QqqlGaugeRegroup.linearEquiv_apply,
  GUT.QqqlGaugeRegroup.phases => Physics.QqqlGaugeRegroup.phases,
  GUT.QqqlGaugeRegroup.regrouped => Physics.QqqlGaugeRegroup.regrouped,
  GUT.QqqlGaugeRegroup.representation => Physics.QqqlGaugeRegroup.representation
]

assert_compatible GUT.QqqlGaugeRegroup.equiv => Physics.QqqlGaugeRegroup.equiv
assert_compatible GUT.QqqlGaugeRegroup.linearEquiv => Physics.QqqlGaugeRegroup.linearEquiv
assert_compatible GUT.QqqlGaugeRegroup.linearEquiv_apply => Physics.QqqlGaugeRegroup.linearEquiv_apply
assert_compatible GUT.QqqlGaugeRegroup.phases => Physics.QqqlGaugeRegroup.phases
assert_compatible GUT.QqqlGaugeRegroup.regrouped => Physics.QqqlGaugeRegroup.regrouped
assert_compatible GUT.QqqlGaugeRegroup.representation => Physics.QqqlGaugeRegroup.representation
