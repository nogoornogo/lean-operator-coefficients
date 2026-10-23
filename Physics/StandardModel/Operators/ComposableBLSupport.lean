import Physics.StandardModel.Operators.Selection.ComposableBLSupport
import Physics.StandardModel.Operators.GradedBnvComparison
import Math.RepresentationTheory.ComposableProtection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ComposableBLSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ComposableBLSupport.Input => Physics.ComposableBLSupport.Input,
  GUT.ComposableBLSupport.Residual => Physics.ComposableBLSupport.Residual,
  GUT.ComposableBLSupport.all_union_forbidden_iff => Physics.ComposableBLSupport.all_union_forbidden_iff,
  GUT.ComposableBLSupport.bOneOrLTwo => Physics.ComposableBLSupport.bOneOrLTwo,
  GUT.ComposableBLSupport.bOneTwo => Physics.ComposableBLSupport.bOneTwo,
  GUT.ComposableBLSupport.bOne_or_bTwo => Physics.ComposableBLSupport.bOne_or_bTwo,
  GUT.ComposableBLSupport.bOne_or_lTwo => Physics.ComposableBLSupport.bOne_or_lTwo,
  GUT.ComposableBLSupport.bosonCharge => Physics.ComposableBLSupport.bosonCharge,
  GUT.ComposableBLSupport.bosonCharge.eq_1 => Physics.ComposableBLSupport.bosonCharge.eq_1,
  GUT.ComposableBLSupport.charge_eq => Physics.ComposableBLSupport.charge_eq,
  GUT.ComposableBLSupport.equiv => Physics.ComposableBLSupport.equiv,
  GUT.ComposableBLSupport.equiv_def => Physics.ComposableBLSupport.equiv_def,
  GUT.ComposableBLSupport.extract_reconstruct => Physics.ComposableBLSupport.extract_reconstruct,
  GUT.ComposableBLSupport.fermionCharge => Physics.ComposableBLSupport.fermionCharge,
  GUT.ComposableBLSupport.fermionCharge.eq_1 => Physics.ComposableBLSupport.fermionCharge.eq_1,
  GUT.ComposableBLSupport.forbidden => Physics.ComposableBLSupport.forbidden,
  GUT.ComposableBLSupport.inputEquiv => Physics.ComposableBLSupport.inputEquiv,
  GUT.ComposableBLSupport.old_support => Physics.ComposableBLSupport.old_support,
  GUT.ComposableBLSupport.reconstruct_extract => Physics.ComposableBLSupport.reconstruct_extract,
  GUT.ComposableBLSupport.specification => Physics.ComposableBLSupport.specification,
  GUT.ComposableBLSupport.union_forbidden_iff => Physics.ComposableBLSupport.union_forbidden_iff
]

assert_compatible GUT.ComposableBLSupport.Input => Physics.ComposableBLSupport.Input
assert_compatible GUT.ComposableBLSupport.Residual => Physics.ComposableBLSupport.Residual
assert_compatible GUT.ComposableBLSupport.all_union_forbidden_iff => Physics.ComposableBLSupport.all_union_forbidden_iff
assert_compatible GUT.ComposableBLSupport.bOneOrLTwo => Physics.ComposableBLSupport.bOneOrLTwo
assert_compatible GUT.ComposableBLSupport.bOneTwo => Physics.ComposableBLSupport.bOneTwo
assert_compatible GUT.ComposableBLSupport.bOne_or_bTwo => Physics.ComposableBLSupport.bOne_or_bTwo
assert_compatible GUT.ComposableBLSupport.bOne_or_lTwo => Physics.ComposableBLSupport.bOne_or_lTwo
assert_compatible GUT.ComposableBLSupport.bosonCharge => Physics.ComposableBLSupport.bosonCharge
assert_compatible GUT.ComposableBLSupport.bosonCharge.eq_1 => Physics.ComposableBLSupport.bosonCharge.eq_1
assert_compatible GUT.ComposableBLSupport.charge_eq => Physics.ComposableBLSupport.charge_eq
assert_compatible GUT.ComposableBLSupport.equiv => Physics.ComposableBLSupport.equiv
assert_compatible GUT.ComposableBLSupport.equiv_def => Physics.ComposableBLSupport.equiv_def
assert_compatible GUT.ComposableBLSupport.extract_reconstruct => Physics.ComposableBLSupport.extract_reconstruct
assert_compatible GUT.ComposableBLSupport.fermionCharge => Physics.ComposableBLSupport.fermionCharge
assert_compatible GUT.ComposableBLSupport.fermionCharge.eq_1 => Physics.ComposableBLSupport.fermionCharge.eq_1
assert_compatible GUT.ComposableBLSupport.forbidden => Physics.ComposableBLSupport.forbidden
assert_compatible GUT.ComposableBLSupport.inputEquiv => Physics.ComposableBLSupport.inputEquiv
assert_compatible GUT.ComposableBLSupport.old_support => Physics.ComposableBLSupport.old_support
assert_compatible GUT.ComposableBLSupport.reconstruct_extract => Physics.ComposableBLSupport.reconstruct_extract
assert_compatible GUT.ComposableBLSupport.specification => Physics.ComposableBLSupport.specification
assert_compatible GUT.ComposableBLSupport.union_forbidden_iff => Physics.ComposableBLSupport.union_forbidden_iff
