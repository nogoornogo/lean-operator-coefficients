import Physics.StandardModel.Operators.BaryonOne.Qque.NeutralQqueExterior
import Physics.StandardModel.Operators.QqueSpinorExterior
import Physics.StandardModel.Gauge.ResidualGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.NeutralQqueExterior instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NeutralQqueExterior.chargedEquiv => Physics.NeutralQqueExterior.chargedEquiv,
  GUT.NeutralQqueExterior.charged_apply => Physics.NeutralQqueExterior.charged_apply,
  GUT.NeutralQqueExterior.charged_dual => Physics.NeutralQqueExterior.charged_dual,
  GUT.NeutralQqueExterior.coefficient => Physics.NeutralQqueExterior.coefficient,
  GUT.NeutralQqueExterior.coefficient_nonzero => Physics.NeutralQqueExterior.coefficient_nonzero,
  GUT.NeutralQqueExterior.coefficient_witness => Physics.NeutralQqueExterior.coefficient_witness,
  GUT.NeutralQqueExterior.e => Physics.NeutralQqueExterior.e,
  GUT.NeutralQqueExterior.exists_of_pointwise_block => Physics.NeutralQqueExterior.exists_of_pointwise_block,
  GUT.NeutralQqueExterior.exists_on_fields => Physics.NeutralQqueExterior.exists_on_fields,
  GUT.NeutralQqueExterior.has_nonzero_alternation => Physics.NeutralQqueExterior.has_nonzero_alternation,
  GUT.NeutralQqueExterior.instAddCommGroupQuark => Physics.NeutralQqueExterior.instAddCommGroupQuark,
  GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexColorSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexColorSpace,
  GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexQuarkSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexQuarkSpace,
  GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexSpace,
  GUT.NeutralQqueExterior.neutral_of_pointwise_block => Physics.NeutralQqueExterior.neutral_of_pointwise_block,
  GUT.NeutralQqueExterior.q => Physics.NeutralQqueExterior.q,
  GUT.NeutralQqueExterior.u => Physics.NeutralQqueExterior.u,
  GUT.NeutralQqueExterior.witness => Physics.NeutralQqueExterior.witness,
  GUT.NeutralQqueExterior.witness.eq_1 => Physics.NeutralQqueExterior.witness.eq_1,
  GUT.StandardSMResidualTensor.qqueIntertwiner.eq_1 => Physics.StandardSMResidualTensor.qqueIntertwiner.eq_1
]

assert_compatible GUT.NeutralQqueExterior.chargedEquiv => Physics.NeutralQqueExterior.chargedEquiv
assert_compatible GUT.NeutralQqueExterior.charged_apply => Physics.NeutralQqueExterior.charged_apply
assert_compatible GUT.NeutralQqueExterior.charged_dual => Physics.NeutralQqueExterior.charged_dual
assert_compatible GUT.NeutralQqueExterior.coefficient => Physics.NeutralQqueExterior.coefficient
assert_compatible GUT.NeutralQqueExterior.coefficient_nonzero => Physics.NeutralQqueExterior.coefficient_nonzero
assert_compatible GUT.NeutralQqueExterior.coefficient_witness => Physics.NeutralQqueExterior.coefficient_witness
assert_compatible GUT.NeutralQqueExterior.e => Physics.NeutralQqueExterior.e
assert_compatible GUT.NeutralQqueExterior.exists_of_pointwise_block => Physics.NeutralQqueExterior.exists_of_pointwise_block
assert_compatible GUT.NeutralQqueExterior.exists_on_fields => Physics.NeutralQqueExterior.exists_on_fields
assert_compatible GUT.NeutralQqueExterior.has_nonzero_alternation => Physics.NeutralQqueExterior.has_nonzero_alternation
assert_compatible GUT.NeutralQqueExterior.instAddCommGroupQuark => Physics.NeutralQqueExterior.instAddCommGroupQuark
assert_compatible GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexColorSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexColorSpace
assert_compatible GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexQuarkSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexQuarkSpace
assert_compatible GUT.NeutralQqueExterior.instAddCommGroupTensorProductComplexSpace => Physics.NeutralQqueExterior.instAddCommGroupTensorProductComplexSpace
assert_compatible GUT.NeutralQqueExterior.neutral_of_pointwise_block => Physics.NeutralQqueExterior.neutral_of_pointwise_block
assert_compatible GUT.NeutralQqueExterior.q => Physics.NeutralQqueExterior.q
assert_compatible GUT.NeutralQqueExterior.u => Physics.NeutralQqueExterior.u
assert_compatible GUT.NeutralQqueExterior.witness => Physics.NeutralQqueExterior.witness
assert_compatible GUT.NeutralQqueExterior.witness.eq_1 => Physics.NeutralQqueExterior.witness.eq_1
assert_compatible GUT.StandardSMResidualTensor.qqueIntertwiner.eq_1 => Physics.StandardSMResidualTensor.qqueIntertwiner.eq_1
