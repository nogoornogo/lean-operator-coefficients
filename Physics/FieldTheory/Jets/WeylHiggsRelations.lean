import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsRelations
import Physics.FieldTheory.Jets.WeylHiggsCurrent
import Physics.FieldTheory.Jets.DerivativeLiteratureRecheck
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsRelations instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsInput.equations.eq_1 => Physics.WeylHiggsInput.equations.eq_1,
  GUT.WeylHiggsRelations.coefficientEquiv => Physics.WeylHiggsRelations.coefficientEquiv,
  GUT.WeylHiggsRelations.componentSeed => Physics.WeylHiggsRelations.componentSeed,
  GUT.WeylHiggsRelations.componentSeed.eq_1 => Physics.WeylHiggsRelations.componentSeed.eq_1,
  GUT.WeylHiggsRelations.component_closure => Physics.WeylHiggsRelations.component_closure,
  GUT.WeylHiggsRelations.component_span => Physics.WeylHiggsRelations.component_span,
  GUT.WeylHiggsRelations.conserved_products => Physics.WeylHiggsRelations.conserved_products,
  GUT.WeylHiggsRelations.current_ibp => Physics.WeylHiggsRelations.current_ibp,
  GUT.WeylHiggsRelations.extraction => Physics.WeylHiggsRelations.extraction,
  GUT.WeylHiggsRelations.generated => Physics.WeylHiggsRelations.generated,
  GUT.WeylHiggsRelations.generatedSeed => Physics.WeylHiggsRelations.generatedSeed,
  GUT.WeylHiggsRelations.generatedSeed.eq_1 => Physics.WeylHiggsRelations.generatedSeed.eq_1,
  GUT.WeylHiggsRelations.generated_even => Physics.WeylHiggsRelations.generated_even,
  GUT.WeylHiggsRelations.generated_odd => Physics.WeylHiggsRelations.generated_odd,
  GUT.WeylHiggsRelations.generated_relations => Physics.WeylHiggsRelations.generated_relations,
  GUT.WeylHiggsRelations.generated_span => Physics.WeylHiggsRelations.generated_span,
  GUT.WeylHiggsRelations.instAddCommGroupA_physics => Physics.WeylHiggsRelations.instAddCommGroupA_physics,
  GUT.WeylHiggsRelations.instModuleComplexA_physics => Physics.WeylHiggsRelations.instModuleComplexA_physics,
  GUT.WeylHiggsRelations.instRingA_physics => Physics.WeylHiggsRelations.instRingA_physics,
  GUT.WeylHiggsRelations.paired_relations => Physics.WeylHiggsRelations.paired_relations,
  GUT.WeylHiggsRelations.symmetric_current_zero => Physics.WeylHiggsRelations.symmetric_current_zero
]

assert_compatible GUT.WeylHiggsInput.equations.eq_1 => Physics.WeylHiggsInput.equations.eq_1
assert_compatible GUT.WeylHiggsRelations.coefficientEquiv => Physics.WeylHiggsRelations.coefficientEquiv
assert_compatible GUT.WeylHiggsRelations.componentSeed => Physics.WeylHiggsRelations.componentSeed
assert_compatible GUT.WeylHiggsRelations.componentSeed.eq_1 => Physics.WeylHiggsRelations.componentSeed.eq_1
assert_compatible GUT.WeylHiggsRelations.component_closure => Physics.WeylHiggsRelations.component_closure
assert_compatible GUT.WeylHiggsRelations.component_span => Physics.WeylHiggsRelations.component_span
assert_compatible GUT.WeylHiggsRelations.conserved_products => Physics.WeylHiggsRelations.conserved_products
assert_compatible GUT.WeylHiggsRelations.current_ibp => Physics.WeylHiggsRelations.current_ibp
assert_compatible GUT.WeylHiggsRelations.extraction => Physics.WeylHiggsRelations.extraction
assert_compatible GUT.WeylHiggsRelations.generated => Physics.WeylHiggsRelations.generated
assert_compatible GUT.WeylHiggsRelations.generatedSeed => Physics.WeylHiggsRelations.generatedSeed
assert_compatible GUT.WeylHiggsRelations.generatedSeed.eq_1 => Physics.WeylHiggsRelations.generatedSeed.eq_1
assert_compatible GUT.WeylHiggsRelations.generated_even => Physics.WeylHiggsRelations.generated_even
assert_compatible GUT.WeylHiggsRelations.generated_odd => Physics.WeylHiggsRelations.generated_odd
assert_compatible GUT.WeylHiggsRelations.generated_relations => Physics.WeylHiggsRelations.generated_relations
assert_compatible GUT.WeylHiggsRelations.generated_span => Physics.WeylHiggsRelations.generated_span
assert_compatible GUT.WeylHiggsRelations.instAddCommGroupA_physics => Physics.WeylHiggsRelations.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsRelations.instModuleComplexA_physics => Physics.WeylHiggsRelations.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsRelations.instRingA_physics => Physics.WeylHiggsRelations.instRingA_physics
assert_compatible GUT.WeylHiggsRelations.paired_relations => Physics.WeylHiggsRelations.paired_relations
assert_compatible GUT.WeylHiggsRelations.symmetric_current_zero => Physics.WeylHiggsRelations.symmetric_current_zero
