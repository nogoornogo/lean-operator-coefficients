import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaDiagonal
import Physics.FieldTheory.Mass.FlavorMajoranaLine
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Flavor.FlavorMajoranaDiagonal instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavorMajoranaDiagonal.coupling => Physics.FlavorMajoranaDiagonal.coupling,
  GUT.FlavorMajoranaDiagonal.coupling.eq_1 => Physics.FlavorMajoranaDiagonal.coupling.eq_1,
  GUT.FlavorMajoranaDiagonal.coupling_evaluation => Physics.FlavorMajoranaDiagonal.coupling_evaluation,
  GUT.FlavorMajoranaDiagonal.coupling_subgroup => Physics.FlavorMajoranaDiagonal.coupling_subgroup,
  GUT.FlavorMajoranaDiagonal.evaluation_eq => Physics.FlavorMajoranaDiagonal.evaluation_eq,
  GUT.FlavorMajoranaDiagonal.evaluation_eq_iff => Physics.FlavorMajoranaDiagonal.evaluation_eq_iff,
  GUT.FlavorMajoranaDiagonal.evaluation_le => Physics.FlavorMajoranaDiagonal.evaluation_le,
  GUT.FlavorMajoranaDiagonal.form => Physics.FlavorMajoranaDiagonal.form,
  GUT.FlavorMajoranaDiagonal.form.eq_1 => Physics.FlavorMajoranaDiagonal.form.eq_1,
  GUT.FlavorMajoranaDiagonal.form_apply => Physics.FlavorMajoranaDiagonal.form_apply,
  GUT.FlavorMajoranaDiagonal.form_symmetric => Physics.FlavorMajoranaDiagonal.form_symmetric,
  GUT.FlavorMajoranaDiagonal.mem_iff => Physics.FlavorMajoranaDiagonal.mem_iff,
  GUT.FlavorMajoranaDiagonal.membership => Physics.FlavorMajoranaDiagonal.membership,
  GUT.FlavorMajoranaDiagonal.mixedEquiv => Physics.FlavorMajoranaDiagonal.mixedEquiv,
  GUT.FlavorMajoranaDiagonal.nonzeroEquiv => Physics.FlavorMajoranaDiagonal.nonzeroEquiv,
  GUT.FlavorMajoranaDiagonal.nonzero_card => Physics.FlavorMajoranaDiagonal.nonzero_card,
  GUT.FlavorMajoranaDiagonal.phaseAction => Physics.FlavorMajoranaDiagonal.phaseAction,
  GUT.FlavorMajoranaDiagonal.phaseAction.eq_1 => Physics.FlavorMajoranaDiagonal.phaseAction.eq_1,
  GUT.FlavorMajoranaDiagonal.productEquiv => Physics.FlavorMajoranaDiagonal.productEquiv,
  GUT.FlavorMajoranaDiagonal.residualHomEquiv => Physics.FlavorMajoranaDiagonal.residualHomEquiv,
  GUT.FlavorMajoranaDiagonal.residual_nonzero_iff => Physics.FlavorMajoranaDiagonal.residual_nonzero_iff,
  GUT.FlavorMajoranaDiagonal.subgroup => Physics.FlavorMajoranaDiagonal.subgroup,
  GUT.FlavorMajoranaDiagonal.subgroup.eq_1 => Physics.FlavorMajoranaDiagonal.subgroup.eq_1,
  GUT.FlavorMajoranaDiagonal.zeroFactorEquiv => Physics.FlavorMajoranaDiagonal.zeroFactorEquiv,
  GUT.FlavorMajoranaDiagonal.zeroFactorEquiv.congr_simp => Physics.FlavorMajoranaDiagonal.zeroFactorEquiv.congr_simp,
  GUT.FlavorMajoranaDiagonal.zero_subgroup => Physics.FlavorMajoranaDiagonal.zero_subgroup,
  GUT.FlavorMajoranaLine.cyclicEquiv.congr_simp => Physics.FlavorMajoranaLine.cyclicEquiv.congr_simp
]

assert_compatible GUT.FlavorMajoranaDiagonal.coupling => Physics.FlavorMajoranaDiagonal.coupling
assert_compatible GUT.FlavorMajoranaDiagonal.coupling.eq_1 => Physics.FlavorMajoranaDiagonal.coupling.eq_1
assert_compatible GUT.FlavorMajoranaDiagonal.coupling_evaluation => Physics.FlavorMajoranaDiagonal.coupling_evaluation
assert_compatible GUT.FlavorMajoranaDiagonal.coupling_subgroup => Physics.FlavorMajoranaDiagonal.coupling_subgroup
assert_compatible GUT.FlavorMajoranaDiagonal.evaluation_eq => Physics.FlavorMajoranaDiagonal.evaluation_eq
assert_compatible GUT.FlavorMajoranaDiagonal.evaluation_eq_iff => Physics.FlavorMajoranaDiagonal.evaluation_eq_iff
assert_compatible GUT.FlavorMajoranaDiagonal.evaluation_le => Physics.FlavorMajoranaDiagonal.evaluation_le
assert_compatible GUT.FlavorMajoranaDiagonal.form => Physics.FlavorMajoranaDiagonal.form
assert_compatible GUT.FlavorMajoranaDiagonal.form.eq_1 => Physics.FlavorMajoranaDiagonal.form.eq_1
assert_compatible GUT.FlavorMajoranaDiagonal.form_apply => Physics.FlavorMajoranaDiagonal.form_apply
assert_compatible GUT.FlavorMajoranaDiagonal.form_symmetric => Physics.FlavorMajoranaDiagonal.form_symmetric
assert_compatible GUT.FlavorMajoranaDiagonal.mem_iff => Physics.FlavorMajoranaDiagonal.mem_iff
assert_compatible GUT.FlavorMajoranaDiagonal.membership => Physics.FlavorMajoranaDiagonal.membership
assert_compatible GUT.FlavorMajoranaDiagonal.mixedEquiv => Physics.FlavorMajoranaDiagonal.mixedEquiv
assert_compatible GUT.FlavorMajoranaDiagonal.nonzeroEquiv => Physics.FlavorMajoranaDiagonal.nonzeroEquiv
assert_compatible GUT.FlavorMajoranaDiagonal.nonzero_card => Physics.FlavorMajoranaDiagonal.nonzero_card
assert_compatible GUT.FlavorMajoranaDiagonal.phaseAction => Physics.FlavorMajoranaDiagonal.phaseAction
assert_compatible GUT.FlavorMajoranaDiagonal.phaseAction.eq_1 => Physics.FlavorMajoranaDiagonal.phaseAction.eq_1
assert_compatible GUT.FlavorMajoranaDiagonal.productEquiv => Physics.FlavorMajoranaDiagonal.productEquiv
assert_compatible GUT.FlavorMajoranaDiagonal.residualHomEquiv => Physics.FlavorMajoranaDiagonal.residualHomEquiv
assert_compatible GUT.FlavorMajoranaDiagonal.residual_nonzero_iff => Physics.FlavorMajoranaDiagonal.residual_nonzero_iff
assert_compatible GUT.FlavorMajoranaDiagonal.subgroup => Physics.FlavorMajoranaDiagonal.subgroup
assert_compatible GUT.FlavorMajoranaDiagonal.subgroup.eq_1 => Physics.FlavorMajoranaDiagonal.subgroup.eq_1
assert_compatible GUT.FlavorMajoranaDiagonal.zeroFactorEquiv => Physics.FlavorMajoranaDiagonal.zeroFactorEquiv
assert_compatible GUT.FlavorMajoranaDiagonal.zeroFactorEquiv.congr_simp => Physics.FlavorMajoranaDiagonal.zeroFactorEquiv.congr_simp
assert_compatible GUT.FlavorMajoranaDiagonal.zero_subgroup => Physics.FlavorMajoranaDiagonal.zero_subgroup
assert_compatible GUT.FlavorMajoranaLine.cyclicEquiv.congr_simp => Physics.FlavorMajoranaLine.cyclicEquiv.congr_simp
