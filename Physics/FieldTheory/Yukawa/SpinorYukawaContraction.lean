import Physics.FieldTheory.Yukawa.Mass.SpinorYukawaContraction
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.FieldTheory.Yukawa.TwoSpeciesExteriorYukawa
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.SpinorYukawaContraction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SpinorYukawaContraction.exterior => Physics.SpinorYukawaContraction.exterior,
  GUT.SpinorYukawaContraction.exterior_nonzero => Physics.SpinorYukawaContraction.exterior_nonzero,
  GUT.SpinorYukawaContraction.ordered => Physics.SpinorYukawaContraction.ordered,
  GUT.SpinorYukawaContraction.ordered.eq_1 => Physics.SpinorYukawaContraction.ordered.eq_1,
  GUT.SpinorYukawaContraction.ordered_apply => Physics.SpinorYukawaContraction.ordered_apply,
  GUT.SpinorYukawaContraction.regroup => Physics.SpinorYukawaContraction.regroup,
  GUT.SpinorYukawaContraction.regroup.eq_1 => Physics.SpinorYukawaContraction.regroup.eq_1,
  GUT.SpinorYukawaContraction.scalarEquiv => Physics.SpinorYukawaContraction.scalarEquiv,
  GUT.SpinorYukawaContraction.scalarEquiv.eq_1 => Physics.SpinorYukawaContraction.scalarEquiv.eq_1
]

assert_compatible GUT.SpinorYukawaContraction.exterior => Physics.SpinorYukawaContraction.exterior
assert_compatible GUT.SpinorYukawaContraction.exterior_nonzero => Physics.SpinorYukawaContraction.exterior_nonzero
assert_compatible GUT.SpinorYukawaContraction.ordered => Physics.SpinorYukawaContraction.ordered
assert_compatible GUT.SpinorYukawaContraction.ordered.eq_1 => Physics.SpinorYukawaContraction.ordered.eq_1
assert_compatible GUT.SpinorYukawaContraction.ordered_apply => Physics.SpinorYukawaContraction.ordered_apply
assert_compatible GUT.SpinorYukawaContraction.regroup => Physics.SpinorYukawaContraction.regroup
assert_compatible GUT.SpinorYukawaContraction.regroup.eq_1 => Physics.SpinorYukawaContraction.regroup.eq_1
assert_compatible GUT.SpinorYukawaContraction.scalarEquiv => Physics.SpinorYukawaContraction.scalarEquiv
assert_compatible GUT.SpinorYukawaContraction.scalarEquiv.eq_1 => Physics.SpinorYukawaContraction.scalarEquiv.eq_1
