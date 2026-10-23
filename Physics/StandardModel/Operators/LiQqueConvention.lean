import Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueConvention
import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiQqueConvention.candidate => Physics.LiQqueConvention.candidate,
  GUT.LiQqueConvention.candidate_eq => Physics.LiQqueConvention.candidate_eq,
  GUT.LiQqueConvention.candidate_fromHom_eq => Physics.LiQqueConvention.candidate_fromHom_eq,
  GUT.LiQqueConvention.candidate_probe => Physics.LiQqueConvention.candidate_probe,
  GUT.LiQqueConvention.daggerTransport => Physics.LiQqueConvention.daggerTransport,
  GUT.LiQqueConvention.ec => Physics.LiQqueConvention.ec,
  GUT.LiQqueConvention.ecDagger => Physics.LiQqueConvention.ecDagger,
  GUT.LiQqueConvention.ecDaggerEquiv => Physics.LiQqueConvention.ecDaggerEquiv,
  GUT.LiQqueConvention.equiv => Physics.LiQqueConvention.equiv,
  GUT.LiQqueConvention.equiv_apply => Physics.LiQqueConvention.equiv_apply,
  GUT.LiQqueConvention.fermionic_reorder => Physics.LiQqueConvention.fermionic_reorder,
  GUT.LiQqueConvention.instAddCommGroupQuark => Physics.LiQqueConvention.instAddCommGroupQuark,
  GUT.LiQqueConvention.instAddCommGroupTensorProductComplexColorDual => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexColorDual,
  GUT.LiQqueConvention.instAddCommGroupTensorProductComplexDual_physics => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexDual_physics,
  GUT.LiQqueConvention.instAddCommGroupTensorProductComplexQuark => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexQuark,
  GUT.LiQqueConvention.onDaggerFieldsEquiv => Physics.LiQqueConvention.onDaggerFieldsEquiv,
  GUT.LiQqueConvention.onDaggerFields_candidate => Physics.LiQqueConvention.onDaggerFields_candidate,
  GUT.LiQqueConvention.paperOrdered => Physics.LiQqueConvention.paperOrdered,
  GUT.LiQqueConvention.paperOrdered_apply => Physics.LiQqueConvention.paperOrdered_apply,
  GUT.LiQqueConvention.singletSwap => Physics.LiQqueConvention.singletSwap,
  GUT.LiQqueConvention.uc => Physics.LiQqueConvention.uc,
  GUT.LiQqueConvention.ucDagger => Physics.LiQqueConvention.ucDagger,
  GUT.LiQqueConvention.ucDaggerEquiv => Physics.LiQqueConvention.ucDaggerEquiv
]

assert_compatible GUT.LiQqueConvention.candidate => Physics.LiQqueConvention.candidate
assert_compatible GUT.LiQqueConvention.candidate_eq => Physics.LiQqueConvention.candidate_eq
assert_compatible GUT.LiQqueConvention.candidate_fromHom_eq => Physics.LiQqueConvention.candidate_fromHom_eq
assert_compatible GUT.LiQqueConvention.candidate_probe => Physics.LiQqueConvention.candidate_probe
assert_compatible GUT.LiQqueConvention.daggerTransport => Physics.LiQqueConvention.daggerTransport
assert_compatible GUT.LiQqueConvention.ec => Physics.LiQqueConvention.ec
assert_compatible GUT.LiQqueConvention.ecDagger => Physics.LiQqueConvention.ecDagger
assert_compatible GUT.LiQqueConvention.ecDaggerEquiv => Physics.LiQqueConvention.ecDaggerEquiv
assert_compatible GUT.LiQqueConvention.equiv => Physics.LiQqueConvention.equiv
assert_compatible GUT.LiQqueConvention.equiv_apply => Physics.LiQqueConvention.equiv_apply
assert_compatible GUT.LiQqueConvention.fermionic_reorder => Physics.LiQqueConvention.fermionic_reorder
assert_compatible GUT.LiQqueConvention.instAddCommGroupQuark => Physics.LiQqueConvention.instAddCommGroupQuark
assert_compatible GUT.LiQqueConvention.instAddCommGroupTensorProductComplexColorDual => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexColorDual
assert_compatible GUT.LiQqueConvention.instAddCommGroupTensorProductComplexDual_physics => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexDual_physics
assert_compatible GUT.LiQqueConvention.instAddCommGroupTensorProductComplexQuark => Physics.LiQqueConvention.instAddCommGroupTensorProductComplexQuark
assert_compatible GUT.LiQqueConvention.onDaggerFieldsEquiv => Physics.LiQqueConvention.onDaggerFieldsEquiv
assert_compatible GUT.LiQqueConvention.onDaggerFields_candidate => Physics.LiQqueConvention.onDaggerFields_candidate
assert_compatible GUT.LiQqueConvention.paperOrdered => Physics.LiQqueConvention.paperOrdered
assert_compatible GUT.LiQqueConvention.paperOrdered_apply => Physics.LiQqueConvention.paperOrdered_apply
assert_compatible GUT.LiQqueConvention.singletSwap => Physics.LiQqueConvention.singletSwap
assert_compatible GUT.LiQqueConvention.uc => Physics.LiQqueConvention.uc
assert_compatible GUT.LiQqueConvention.ucDagger => Physics.LiQqueConvention.ucDagger
assert_compatible GUT.LiQqueConvention.ucDaggerEquiv => Physics.LiQqueConvention.ucDaggerEquiv
