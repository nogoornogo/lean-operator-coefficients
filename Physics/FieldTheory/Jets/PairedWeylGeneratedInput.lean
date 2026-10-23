import Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput
import Physics.FieldTheory.Jets.PairedWeylInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.PairedWeylGeneratedInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairedWeylInput.candidate_extraction => Physics.PairedWeylInput.candidate_extraction,
  GUT.PairedWeylInput.closure_equal => Physics.PairedWeylInput.closure_equal,
  GUT.PairedWeylInput.coefficientEquiv => Physics.PairedWeylInput.coefficientEquiv,
  GUT.PairedWeylInput.component_mem_span => Physics.PairedWeylInput.component_mem_span,
  GUT.PairedWeylInput.current_ibp => Physics.PairedWeylInput.current_ibp,
  GUT.PairedWeylInput.equation_expansion => Physics.PairedWeylInput.equation_expansion,
  GUT.PairedWeylInput.equation_span => Physics.PairedWeylInput.equation_span,
  GUT.PairedWeylInput.evaluation_agrees => Physics.PairedWeylInput.evaluation_agrees,
  GUT.PairedWeylInput.generated => Physics.PairedWeylInput.generated,
  GUT.PairedWeylInput.generated_relations => Physics.PairedWeylInput.generated_relations,
  GUT.PairedWeylInput.instAddCommGroupA_physics_1 => Physics.PairedWeylInput.instAddCommGroupA_physics_1,
  GUT.PairedWeylInput.instModuleComplexA_physics_1 => Physics.PairedWeylInput.instModuleComplexA_physics_1,
  GUT.PairedWeylInput.instRingA_physics_1 => Physics.PairedWeylInput.instRingA_physics_1,
  GUT.PairedWeylInput.left_mem_span => Physics.PairedWeylInput.left_mem_span,
  GUT.PairedWeylInput.left_row => Physics.PairedWeylInput.left_row,
  GUT.PairedWeylInput.oddInc_X => Physics.PairedWeylInput.oddInc_X,
  GUT.PairedWeylInput.right_mem_span => Physics.PairedWeylInput.right_mem_span,
  GUT.PairedWeylInput.right_row => Physics.PairedWeylInput.right_row,
  GUT.PairedWeylInput.seed_zero => Physics.PairedWeylInput.seed_zero,
  GUT.PairedWeylInput.toDirect => Physics.PairedWeylInput.toDirect,
  GUT.PairedWeylInput.toGenerated => Physics.PairedWeylInput.toGenerated
]

assert_compatible GUT.PairedWeylInput.candidate_extraction => Physics.PairedWeylInput.candidate_extraction
assert_compatible GUT.PairedWeylInput.closure_equal => Physics.PairedWeylInput.closure_equal
assert_compatible GUT.PairedWeylInput.coefficientEquiv => Physics.PairedWeylInput.coefficientEquiv
assert_compatible GUT.PairedWeylInput.component_mem_span => Physics.PairedWeylInput.component_mem_span
assert_compatible GUT.PairedWeylInput.current_ibp => Physics.PairedWeylInput.current_ibp
assert_compatible GUT.PairedWeylInput.equation_expansion => Physics.PairedWeylInput.equation_expansion
assert_compatible GUT.PairedWeylInput.equation_span => Physics.PairedWeylInput.equation_span
assert_compatible GUT.PairedWeylInput.evaluation_agrees => Physics.PairedWeylInput.evaluation_agrees
assert_compatible GUT.PairedWeylInput.generated => Physics.PairedWeylInput.generated
assert_compatible GUT.PairedWeylInput.generated_relations => Physics.PairedWeylInput.generated_relations
assert_compatible GUT.PairedWeylInput.instAddCommGroupA_physics_1 => Physics.PairedWeylInput.instAddCommGroupA_physics_1
assert_compatible GUT.PairedWeylInput.instModuleComplexA_physics_1 => Physics.PairedWeylInput.instModuleComplexA_physics_1
assert_compatible GUT.PairedWeylInput.instRingA_physics_1 => Physics.PairedWeylInput.instRingA_physics_1
assert_compatible GUT.PairedWeylInput.left_mem_span => Physics.PairedWeylInput.left_mem_span
assert_compatible GUT.PairedWeylInput.left_row => Physics.PairedWeylInput.left_row
assert_compatible GUT.PairedWeylInput.oddInc_X => Physics.PairedWeylInput.oddInc_X
assert_compatible GUT.PairedWeylInput.right_mem_span => Physics.PairedWeylInput.right_mem_span
assert_compatible GUT.PairedWeylInput.right_row => Physics.PairedWeylInput.right_row
assert_compatible GUT.PairedWeylInput.seed_zero => Physics.PairedWeylInput.seed_zero
assert_compatible GUT.PairedWeylInput.toDirect => Physics.PairedWeylInput.toDirect
assert_compatible GUT.PairedWeylInput.toGenerated => Physics.PairedWeylInput.toGenerated
