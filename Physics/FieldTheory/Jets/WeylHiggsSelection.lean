import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsSelection
import Physics.FieldTheory.Jets.WeylHiggsRelations
import Math.Algebra.MixedJetFinite
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsSelection.candidate => Physics.WeylHiggsSelection.candidate,
  GUT.WeylHiggsSelection.candidate_fixed => Physics.WeylHiggsSelection.candidate_fixed,
  GUT.WeylHiggsSelection.candidate_grade => Physics.WeylHiggsSelection.candidate_grade,
  GUT.WeylHiggsSelection.current_grade => Physics.WeylHiggsSelection.current_grade,
  GUT.WeylHiggsSelection.evaluate => Physics.WeylHiggsSelection.evaluate,
  GUT.WeylHiggsSelection.generatedSelected => Physics.WeylHiggsSelection.generatedSelected,
  GUT.WeylHiggsSelection.h_grade => Physics.WeylHiggsSelection.h_grade,
  GUT.WeylHiggsSelection.higgs_current_grade => Physics.WeylHiggsSelection.higgs_current_grade,
  GUT.WeylHiggsSelection.instAddCommGroupA_physics => Physics.WeylHiggsSelection.instAddCommGroupA_physics,
  GUT.WeylHiggsSelection.instModuleComplexA_physics => Physics.WeylHiggsSelection.instModuleComplexA_physics,
  GUT.WeylHiggsSelection.instRingA_physics => Physics.WeylHiggsSelection.instRingA_physics,
  GUT.WeylHiggsSelection.psi_grade => Physics.WeylHiggsSelection.psi_grade,
  GUT.WeylHiggsSelection.rho_grade => Physics.WeylHiggsSelection.rho_grade,
  GUT.WeylHiggsSelection.selectedCoefficientEquiv => Physics.WeylHiggsSelection.selectedCoefficientEquiv,
  GUT.WeylHiggsSelection.selected_extraction => Physics.WeylHiggsSelection.selected_extraction
]

assert_compatible GUT.WeylHiggsSelection.candidate => Physics.WeylHiggsSelection.candidate
assert_compatible GUT.WeylHiggsSelection.candidate_fixed => Physics.WeylHiggsSelection.candidate_fixed
assert_compatible GUT.WeylHiggsSelection.candidate_grade => Physics.WeylHiggsSelection.candidate_grade
assert_compatible GUT.WeylHiggsSelection.current_grade => Physics.WeylHiggsSelection.current_grade
assert_compatible GUT.WeylHiggsSelection.evaluate => Physics.WeylHiggsSelection.evaluate
assert_compatible GUT.WeylHiggsSelection.generatedSelected => Physics.WeylHiggsSelection.generatedSelected
assert_compatible GUT.WeylHiggsSelection.h_grade => Physics.WeylHiggsSelection.h_grade
assert_compatible GUT.WeylHiggsSelection.higgs_current_grade => Physics.WeylHiggsSelection.higgs_current_grade
assert_compatible GUT.WeylHiggsSelection.instAddCommGroupA_physics => Physics.WeylHiggsSelection.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsSelection.instModuleComplexA_physics => Physics.WeylHiggsSelection.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsSelection.instRingA_physics => Physics.WeylHiggsSelection.instRingA_physics
assert_compatible GUT.WeylHiggsSelection.psi_grade => Physics.WeylHiggsSelection.psi_grade
assert_compatible GUT.WeylHiggsSelection.rho_grade => Physics.WeylHiggsSelection.rho_grade
assert_compatible GUT.WeylHiggsSelection.selectedCoefficientEquiv => Physics.WeylHiggsSelection.selectedCoefficientEquiv
assert_compatible GUT.WeylHiggsSelection.selected_extraction => Physics.WeylHiggsSelection.selected_extraction
