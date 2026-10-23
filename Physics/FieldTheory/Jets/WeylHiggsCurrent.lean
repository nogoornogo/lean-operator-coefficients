import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCurrent
import Physics.FieldTheory.Jets.WeylHiggsInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCurrent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DerivativeLiteratureMixed.candidate.eq_1 => Physics.DerivativeLiteratureMixed.candidate.eq_1,
  GUT.DerivativeLiteratureMixed.h.eq_1 => Physics.DerivativeLiteratureMixed.h.eq_1,
  GUT.DerivativeLiteratureMixed.higgsCurrent.eq_1 => Physics.DerivativeLiteratureMixed.higgsCurrent.eq_1,
  GUT.DerivativeLiteratureMixed.rho.eq_1 => Physics.DerivativeLiteratureMixed.rho.eq_1,
  GUT.WeylHiggsCurrent.action_mul => Physics.WeylHiggsCurrent.action_mul,
  GUT.WeylHiggsCurrent.candidate_invariant => Physics.WeylHiggsCurrent.candidate_invariant,
  GUT.WeylHiggsCurrent.contraction_invariant => Physics.WeylHiggsCurrent.contraction_invariant,
  GUT.WeylHiggsCurrent.current_covariant => Physics.WeylHiggsCurrent.current_covariant,
  GUT.WeylHiggsCurrent.higgs_current_covariant => Physics.WeylHiggsCurrent.higgs_current_covariant,
  GUT.WeylHiggsCurrent.higgs_current_dictionary => Physics.WeylHiggsCurrent.higgs_current_dictionary,
  GUT.WeylHiggsCurrent.instAddCommGroupA_physics => Physics.WeylHiggsCurrent.instAddCommGroupA_physics,
  GUT.WeylHiggsCurrent.instModuleComplexA_physics => Physics.WeylHiggsCurrent.instModuleComplexA_physics,
  GUT.WeylHiggsCurrent.instRingA_physics => Physics.WeylHiggsCurrent.instRingA_physics,
  GUT.WeylHiggsCurrent.inverse_pair => Physics.WeylHiggsCurrent.inverse_pair,
  GUT.WeylHiggsCurrent.matrix_current_covariant => Physics.WeylHiggsCurrent.matrix_current_covariant,
  GUT.WeylHiggsCurrent.phases => Physics.WeylHiggsCurrent.phases,
  GUT.WeylHiggsCurrent.psi_covariant => Physics.WeylHiggsCurrent.psi_covariant,
  GUT.WeylHiggsCurrent.rho_dictionary => Physics.WeylHiggsCurrent.rho_dictionary,
  GUT.WeylHiggsCurrent.rho_invariant => Physics.WeylHiggsCurrent.rho_invariant,
  GUT.WeylHiggsCurrent.scalarCurrent => Physics.WeylHiggsCurrent.scalarCurrent,
  GUT.WeylHiggsCurrent.scalarCurrent.eq_1 => Physics.WeylHiggsCurrent.scalarCurrent.eq_1,
  GUT.WeylHiggsCurrent.scalar_current_covariant => Physics.WeylHiggsCurrent.scalar_current_covariant,
  GUT.WeylHiggsCurrent.scalar_current_internal => Physics.WeylHiggsCurrent.scalar_current_internal,
  GUT.WeylHiggsCurrent.scalar_current_lorentz => Physics.WeylHiggsCurrent.scalar_current_lorentz
]

assert_compatible GUT.DerivativeLiteratureMixed.candidate.eq_1 => Physics.DerivativeLiteratureMixed.candidate.eq_1
assert_compatible GUT.DerivativeLiteratureMixed.h.eq_1 => Physics.DerivativeLiteratureMixed.h.eq_1
assert_compatible GUT.DerivativeLiteratureMixed.higgsCurrent.eq_1 => Physics.DerivativeLiteratureMixed.higgsCurrent.eq_1
assert_compatible GUT.DerivativeLiteratureMixed.rho.eq_1 => Physics.DerivativeLiteratureMixed.rho.eq_1
assert_compatible GUT.WeylHiggsCurrent.action_mul => Physics.WeylHiggsCurrent.action_mul
assert_compatible GUT.WeylHiggsCurrent.candidate_invariant => Physics.WeylHiggsCurrent.candidate_invariant
assert_compatible GUT.WeylHiggsCurrent.contraction_invariant => Physics.WeylHiggsCurrent.contraction_invariant
assert_compatible GUT.WeylHiggsCurrent.current_covariant => Physics.WeylHiggsCurrent.current_covariant
assert_compatible GUT.WeylHiggsCurrent.higgs_current_covariant => Physics.WeylHiggsCurrent.higgs_current_covariant
assert_compatible GUT.WeylHiggsCurrent.higgs_current_dictionary => Physics.WeylHiggsCurrent.higgs_current_dictionary
assert_compatible GUT.WeylHiggsCurrent.instAddCommGroupA_physics => Physics.WeylHiggsCurrent.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsCurrent.instModuleComplexA_physics => Physics.WeylHiggsCurrent.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsCurrent.instRingA_physics => Physics.WeylHiggsCurrent.instRingA_physics
assert_compatible GUT.WeylHiggsCurrent.inverse_pair => Physics.WeylHiggsCurrent.inverse_pair
assert_compatible GUT.WeylHiggsCurrent.matrix_current_covariant => Physics.WeylHiggsCurrent.matrix_current_covariant
assert_compatible GUT.WeylHiggsCurrent.phases => Physics.WeylHiggsCurrent.phases
assert_compatible GUT.WeylHiggsCurrent.psi_covariant => Physics.WeylHiggsCurrent.psi_covariant
assert_compatible GUT.WeylHiggsCurrent.rho_dictionary => Physics.WeylHiggsCurrent.rho_dictionary
assert_compatible GUT.WeylHiggsCurrent.rho_invariant => Physics.WeylHiggsCurrent.rho_invariant
assert_compatible GUT.WeylHiggsCurrent.scalarCurrent => Physics.WeylHiggsCurrent.scalarCurrent
assert_compatible GUT.WeylHiggsCurrent.scalarCurrent.eq_1 => Physics.WeylHiggsCurrent.scalarCurrent.eq_1
assert_compatible GUT.WeylHiggsCurrent.scalar_current_covariant => Physics.WeylHiggsCurrent.scalar_current_covariant
assert_compatible GUT.WeylHiggsCurrent.scalar_current_internal => Physics.WeylHiggsCurrent.scalar_current_internal
assert_compatible GUT.WeylHiggsCurrent.scalar_current_lorentz => Physics.WeylHiggsCurrent.scalar_current_lorentz
