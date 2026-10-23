import Physics.StandardModel.Operators.Selection.QLFiniteSupport
import Physics.StandardModel.Operators.SMFiniteHiggsSupport
import Physics.StandardModel.Operators.DuqlHiggsContent
import Math.RepresentationTheory.ScalarResidualSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.QLFiniteSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QLFiniteSupport.LocalTest => Physics.QLFiniteSupport.LocalTest,
  GUT.QLFiniteSupport.Test => Physics.QLFiniteSupport.Test,
  GUT.QLFiniteSupport.action => Physics.QLFiniteSupport.action,
  GUT.QLFiniteSupport.action_residual => Physics.QLFiniteSupport.action_residual,
  GUT.QLFiniteSupport.boson => Physics.QLFiniteSupport.boson,
  GUT.QLFiniteSupport.boson_residual => Physics.QLFiniteSupport.boson_residual,
  GUT.QLFiniteSupport.character_product => Physics.QLFiniteSupport.character_product,
  GUT.QLFiniteSupport.charge => Physics.QLFiniteSupport.charge,
  GUT.QLFiniteSupport.charge.eq_1 => Physics.QLFiniteSupport.charge.eq_1,
  GUT.QLFiniteSupport.family_charge_controls => Physics.QLFiniteSupport.family_charge_controls,
  GUT.QLFiniteSupport.field_local => Physics.QLFiniteSupport.field_local,
  GUT.QLFiniteSupport.flavor => Physics.QLFiniteSupport.flavor,
  GUT.QLFiniteSupport.flavor.congr_simp => Physics.QLFiniteSupport.flavor.congr_simp,
  GUT.QLFiniteSupport.original_allowed_iff => Physics.QLFiniteSupport.original_allowed_iff,
  GUT.QLFiniteSupport.raw_residual => Physics.QLFiniteSupport.raw_residual,
  GUT.QLFiniteSupport.source => Physics.QLFiniteSupport.source,
  GUT.QLFiniteSupport.source_residual => Physics.QLFiniteSupport.source_residual,
  GUT.QLFiniteSupport.test_allowed_iff => Physics.QLFiniteSupport.test_allowed_iff
]

assert_compatible GUT.QLFiniteSupport.LocalTest => Physics.QLFiniteSupport.LocalTest
assert_compatible GUT.QLFiniteSupport.Test => Physics.QLFiniteSupport.Test
assert_compatible GUT.QLFiniteSupport.action => Physics.QLFiniteSupport.action
assert_compatible GUT.QLFiniteSupport.action_residual => Physics.QLFiniteSupport.action_residual
assert_compatible GUT.QLFiniteSupport.boson => Physics.QLFiniteSupport.boson
assert_compatible GUT.QLFiniteSupport.boson_residual => Physics.QLFiniteSupport.boson_residual
assert_compatible GUT.QLFiniteSupport.character_product => Physics.QLFiniteSupport.character_product
assert_compatible GUT.QLFiniteSupport.charge => Physics.QLFiniteSupport.charge
assert_compatible GUT.QLFiniteSupport.charge.eq_1 => Physics.QLFiniteSupport.charge.eq_1
assert_compatible GUT.QLFiniteSupport.family_charge_controls => Physics.QLFiniteSupport.family_charge_controls
assert_compatible GUT.QLFiniteSupport.field_local => Physics.QLFiniteSupport.field_local
assert_compatible GUT.QLFiniteSupport.flavor => Physics.QLFiniteSupport.flavor
assert_compatible GUT.QLFiniteSupport.flavor.congr_simp => Physics.QLFiniteSupport.flavor.congr_simp
assert_compatible GUT.QLFiniteSupport.original_allowed_iff => Physics.QLFiniteSupport.original_allowed_iff
assert_compatible GUT.QLFiniteSupport.raw_residual => Physics.QLFiniteSupport.raw_residual
assert_compatible GUT.QLFiniteSupport.source => Physics.QLFiniteSupport.source
assert_compatible GUT.QLFiniteSupport.source_residual => Physics.QLFiniteSupport.source_residual
assert_compatible GUT.QLFiniteSupport.test_allowed_iff => Physics.QLFiniteSupport.test_allowed_iff
