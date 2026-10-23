import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck
import Math.RepresentationTheory.FiniteDerivativeScalarControl
import Physics.FieldTheory.Jets.HiggsStandardInput
import Physics.FieldTheory.Jets.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.PairedWeylGeneratedInput
import Physics.FieldTheory.Jets.DerivativeLiteratureScalar
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DerivativeLiteratureMixed.sigma.eq_1 => Physics.DerivativeLiteratureMixed.sigma.eq_1,
  GUT.DerivativeLiteratureRecheck.C1.offCoefficient => Physics.DerivativeLiteratureRecheck.C1.offCoefficient,
  GUT.DerivativeLiteratureRecheck.C1.off_values => Physics.DerivativeLiteratureRecheck.C1.off_values,
  GUT.DerivativeLiteratureRecheck.C1.on_forbidden => Physics.DerivativeLiteratureRecheck.C1.on_forbidden,
  GUT.DerivativeLiteratureRecheck.C2.certified_controls => Physics.DerivativeLiteratureRecheck.C2.certified_controls,
  GUT.DerivativeLiteratureRecheck.C3.coefficient_relation => Physics.DerivativeLiteratureRecheck.C3.coefficient_relation,
  GUT.DerivativeLiteratureRecheck.C3.density => Physics.DerivativeLiteratureRecheck.C3.density,
  GUT.DerivativeLiteratureRecheck.C3.derivative_only_iff => Physics.DerivativeLiteratureRecheck.C3.derivative_only_iff,
  GUT.DerivativeLiteratureRecheck.C3.input => Physics.DerivativeLiteratureRecheck.C3.input,
  GUT.DerivativeLiteratureRecheck.C3.quotient_relation => Physics.DerivativeLiteratureRecheck.C3.quotient_relation,
  GUT.DerivativeLiteratureRecheck.C4.divergenceWitness => Physics.DerivativeLiteratureRecheck.C4.divergenceWitness,
  GUT.DerivativeLiteratureRecheck.C4.raw_independence => Physics.DerivativeLiteratureRecheck.C4.raw_independence,
  GUT.DerivativeLiteratureRecheck.C4.raw_probe_rejected => Physics.DerivativeLiteratureRecheck.C4.raw_probe_rejected,
  GUT.DerivativeLiteratureRecheck.C4.witness_zero => Physics.DerivativeLiteratureRecheck.C4.witness_zero,
  GUT.DerivativeLiteratureRecheck.C5.conserved_products => Physics.DerivativeLiteratureRecheck.C5.conserved_products,
  GUT.DerivativeLiteratureRecheck.C5.currentDivergence => Physics.DerivativeLiteratureRecheck.C5.currentDivergence,
  GUT.DerivativeLiteratureRecheck.C5.currentDivergence.eq_1 => Physics.DerivativeLiteratureRecheck.C5.currentDivergence.eq_1,
  GUT.DerivativeLiteratureRecheck.C5.divergence_eom => Physics.DerivativeLiteratureRecheck.C5.divergence_eom,
  GUT.DerivativeLiteratureRecheck.C5.divergence_identity => Physics.DerivativeLiteratureRecheck.C5.divergence_identity,
  GUT.DerivativeLiteratureRecheck.C5.instAddCommGroupA => Physics.DerivativeLiteratureRecheck.C5.instAddCommGroupA,
  GUT.DerivativeLiteratureRecheck.C5.instModuleComplexA => Physics.DerivativeLiteratureRecheck.C5.instModuleComplexA,
  GUT.DerivativeLiteratureRecheck.C5.instRingA => Physics.DerivativeLiteratureRecheck.C5.instRingA,
  GUT.DerivativeLiteratureRecheck.C5.reorder_value => Physics.DerivativeLiteratureRecheck.C5.reorder_value,
  GUT.DerivativeLiteratureRecheck.C5.symmetric_current_zero => Physics.DerivativeLiteratureRecheck.C5.symmetric_current_zero,
  GUT.DerivativeLiteratureRecheck.C6.generated_first_zero => Physics.DerivativeLiteratureRecheck.C6.generated_first_zero,
  GUT.DerivativeLiteratureRecheck.C6.second_order_control => Physics.DerivativeLiteratureRecheck.C6.second_order_control
]

assert_compatible GUT.DerivativeLiteratureMixed.sigma.eq_1 => Physics.DerivativeLiteratureMixed.sigma.eq_1
assert_compatible GUT.DerivativeLiteratureRecheck.C1.offCoefficient => Physics.DerivativeLiteratureRecheck.C1.offCoefficient
assert_compatible GUT.DerivativeLiteratureRecheck.C1.off_values => Physics.DerivativeLiteratureRecheck.C1.off_values
assert_compatible GUT.DerivativeLiteratureRecheck.C1.on_forbidden => Physics.DerivativeLiteratureRecheck.C1.on_forbidden
assert_compatible GUT.DerivativeLiteratureRecheck.C2.certified_controls => Physics.DerivativeLiteratureRecheck.C2.certified_controls
assert_compatible GUT.DerivativeLiteratureRecheck.C3.coefficient_relation => Physics.DerivativeLiteratureRecheck.C3.coefficient_relation
assert_compatible GUT.DerivativeLiteratureRecheck.C3.density => Physics.DerivativeLiteratureRecheck.C3.density
assert_compatible GUT.DerivativeLiteratureRecheck.C3.derivative_only_iff => Physics.DerivativeLiteratureRecheck.C3.derivative_only_iff
assert_compatible GUT.DerivativeLiteratureRecheck.C3.input => Physics.DerivativeLiteratureRecheck.C3.input
assert_compatible GUT.DerivativeLiteratureRecheck.C3.quotient_relation => Physics.DerivativeLiteratureRecheck.C3.quotient_relation
assert_compatible GUT.DerivativeLiteratureRecheck.C4.divergenceWitness => Physics.DerivativeLiteratureRecheck.C4.divergenceWitness
assert_compatible GUT.DerivativeLiteratureRecheck.C4.raw_independence => Physics.DerivativeLiteratureRecheck.C4.raw_independence
assert_compatible GUT.DerivativeLiteratureRecheck.C4.raw_probe_rejected => Physics.DerivativeLiteratureRecheck.C4.raw_probe_rejected
assert_compatible GUT.DerivativeLiteratureRecheck.C4.witness_zero => Physics.DerivativeLiteratureRecheck.C4.witness_zero
assert_compatible GUT.DerivativeLiteratureRecheck.C5.conserved_products => Physics.DerivativeLiteratureRecheck.C5.conserved_products
assert_compatible GUT.DerivativeLiteratureRecheck.C5.currentDivergence => Physics.DerivativeLiteratureRecheck.C5.currentDivergence
assert_compatible GUT.DerivativeLiteratureRecheck.C5.currentDivergence.eq_1 => Physics.DerivativeLiteratureRecheck.C5.currentDivergence.eq_1
assert_compatible GUT.DerivativeLiteratureRecheck.C5.divergence_eom => Physics.DerivativeLiteratureRecheck.C5.divergence_eom
assert_compatible GUT.DerivativeLiteratureRecheck.C5.divergence_identity => Physics.DerivativeLiteratureRecheck.C5.divergence_identity
assert_compatible GUT.DerivativeLiteratureRecheck.C5.instAddCommGroupA => Physics.DerivativeLiteratureRecheck.C5.instAddCommGroupA
assert_compatible GUT.DerivativeLiteratureRecheck.C5.instModuleComplexA => Physics.DerivativeLiteratureRecheck.C5.instModuleComplexA
assert_compatible GUT.DerivativeLiteratureRecheck.C5.instRingA => Physics.DerivativeLiteratureRecheck.C5.instRingA
assert_compatible GUT.DerivativeLiteratureRecheck.C5.reorder_value => Physics.DerivativeLiteratureRecheck.C5.reorder_value
assert_compatible GUT.DerivativeLiteratureRecheck.C5.symmetric_current_zero => Physics.DerivativeLiteratureRecheck.C5.symmetric_current_zero
assert_compatible GUT.DerivativeLiteratureRecheck.C6.generated_first_zero => Physics.DerivativeLiteratureRecheck.C6.generated_first_zero
assert_compatible GUT.DerivativeLiteratureRecheck.C6.second_order_control => Physics.DerivativeLiteratureRecheck.C6.second_order_control
