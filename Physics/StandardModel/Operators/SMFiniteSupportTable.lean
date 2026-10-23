import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteSupportTable
import Physics.StandardModel.Operators.SMFiniteHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteSupportTable instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteSupportTable.Index => Physics.SMFiniteSupportTable.Index,
  GUT.SMFiniteSupportTable.Pattern => Physics.SMFiniteSupportTable.Pattern,
  GUT.SMFiniteSupportTable.TableTest => Physics.SMFiniteSupportTable.TableTest,
  GUT.SMFiniteSupportTable.all_degrees_iff => Physics.SMFiniteSupportTable.all_degrees_iff,
  GUT.SMFiniteSupportTable.entry => Physics.SMFiniteSupportTable.entry,
  GUT.SMFiniteSupportTable.family_bound_controls => Physics.SMFiniteSupportTable.family_bound_controls,
  GUT.SMFiniteSupportTable.family_charge_controls => Physics.SMFiniteSupportTable.family_charge_controls,
  GUT.SMFiniteSupportTable.finite_universe_iff => Physics.SMFiniteSupportTable.finite_universe_iff,
  GUT.SMFiniteSupportTable.global_table_iff => Physics.SMFiniteSupportTable.global_table_iff,
  GUT.SMFiniteSupportTable.instFintypeIndex => Physics.SMFiniteSupportTable.instFintypeIndex,
  GUT.SMFiniteSupportTable.instFintypePattern => Physics.SMFiniteSupportTable.instFintypePattern,
  GUT.SMFiniteSupportTable.pilot_all_forbidden => Physics.SMFiniteSupportTable.pilot_all_forbidden
]

assert_compatible GUT.SMFiniteSupportTable.Index => Physics.SMFiniteSupportTable.Index
assert_compatible GUT.SMFiniteSupportTable.Pattern => Physics.SMFiniteSupportTable.Pattern
assert_compatible GUT.SMFiniteSupportTable.TableTest => Physics.SMFiniteSupportTable.TableTest
assert_compatible GUT.SMFiniteSupportTable.all_degrees_iff => Physics.SMFiniteSupportTable.all_degrees_iff
assert_compatible GUT.SMFiniteSupportTable.entry => Physics.SMFiniteSupportTable.entry
assert_compatible GUT.SMFiniteSupportTable.family_bound_controls => Physics.SMFiniteSupportTable.family_bound_controls
assert_compatible GUT.SMFiniteSupportTable.family_charge_controls => Physics.SMFiniteSupportTable.family_charge_controls
assert_compatible GUT.SMFiniteSupportTable.finite_universe_iff => Physics.SMFiniteSupportTable.finite_universe_iff
assert_compatible GUT.SMFiniteSupportTable.global_table_iff => Physics.SMFiniteSupportTable.global_table_iff
assert_compatible GUT.SMFiniteSupportTable.instFintypeIndex => Physics.SMFiniteSupportTable.instFintypeIndex
assert_compatible GUT.SMFiniteSupportTable.instFintypePattern => Physics.SMFiniteSupportTable.instFintypePattern
assert_compatible GUT.SMFiniteSupportTable.pilot_all_forbidden => Physics.SMFiniteSupportTable.pilot_all_forbidden
