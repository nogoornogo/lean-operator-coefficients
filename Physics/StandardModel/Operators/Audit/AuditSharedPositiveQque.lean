import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditSharedPositiveQque
import Physics.StandardModel.Operators.SharedPositiveQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditSharedPositiveQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SharedPositiveQqueAudit.characters_differ => Physics.SharedPositiveQqueAudit.characters_differ,
  GUT.SharedPositiveQqueAudit.copies_continuous => Physics.SharedPositiveQqueAudit.copies_continuous,
  GUT.SharedPositiveQqueAudit.difference_realization => Physics.SharedPositiveQqueAudit.difference_realization,
  GUT.SharedPositiveQqueAudit.difference_split => Physics.SharedPositiveQqueAudit.difference_split,
  GUT.SharedPositiveQqueAudit.disjoint => Physics.SharedPositiveQqueAudit.disjoint,
  GUT.SharedPositiveQqueAudit.disjoint.eq_1 => Physics.SharedPositiveQqueAudit.disjoint.eq_1,
  GUT.SharedPositiveQqueAudit.no_shared => Physics.SharedPositiveQqueAudit.no_shared,
  GUT.SharedPositiveQqueAudit.positive_totals_not_enough => Physics.SharedPositiveQqueAudit.positive_totals_not_enough,
  GUT.SharedPositiveQqueAudit.shared => Physics.SharedPositiveQqueAudit.shared,
  GUT.SharedPositiveQqueAudit.totals => Physics.SharedPositiveQqueAudit.totals,
  GUT.SharedPositiveQqueAudit.unequal => Physics.SharedPositiveQqueAudit.unequal,
  GUT.SharedPositiveQqueAudit.unequal.eq_1 => Physics.SharedPositiveQqueAudit.unequal.eq_1
]

assert_compatible GUT.SharedPositiveQqueAudit.characters_differ => Physics.SharedPositiveQqueAudit.characters_differ
assert_compatible GUT.SharedPositiveQqueAudit.copies_continuous => Physics.SharedPositiveQqueAudit.copies_continuous
assert_compatible GUT.SharedPositiveQqueAudit.difference_realization => Physics.SharedPositiveQqueAudit.difference_realization
assert_compatible GUT.SharedPositiveQqueAudit.difference_split => Physics.SharedPositiveQqueAudit.difference_split
assert_compatible GUT.SharedPositiveQqueAudit.disjoint => Physics.SharedPositiveQqueAudit.disjoint
assert_compatible GUT.SharedPositiveQqueAudit.disjoint.eq_1 => Physics.SharedPositiveQqueAudit.disjoint.eq_1
assert_compatible GUT.SharedPositiveQqueAudit.no_shared => Physics.SharedPositiveQqueAudit.no_shared
assert_compatible GUT.SharedPositiveQqueAudit.positive_totals_not_enough => Physics.SharedPositiveQqueAudit.positive_totals_not_enough
assert_compatible GUT.SharedPositiveQqueAudit.shared => Physics.SharedPositiveQqueAudit.shared
assert_compatible GUT.SharedPositiveQqueAudit.totals => Physics.SharedPositiveQqueAudit.totals
assert_compatible GUT.SharedPositiveQqueAudit.unequal => Physics.SharedPositiveQqueAudit.unequal
assert_compatible GUT.SharedPositiveQqueAudit.unequal.eq_1 => Physics.SharedPositiveQqueAudit.unequal.eq_1
