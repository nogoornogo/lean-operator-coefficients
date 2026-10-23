import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditPairwisePositiveQque
import Physics.StandardModel.Operators.PairwisePositiveQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditPairwisePositiveQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairwisePositiveQqueAudit.distinct_quotients => Physics.PairwisePositiveQqueAudit.distinct_quotients,
  GUT.PairwisePositiveQqueAudit.es => Physics.PairwisePositiveQqueAudit.es,
  GUT.PairwisePositiveQqueAudit.instAddCommGroupQuark => Physics.PairwisePositiveQqueAudit.instAddCommGroupQuark,
  GUT.PairwisePositiveQqueAudit.missingElectron => Physics.PairwisePositiveQqueAudit.missingElectron,
  GUT.PairwisePositiveQqueAudit.missing_pair => Physics.PairwisePositiveQqueAudit.missing_pair,
  GUT.PairwisePositiveQqueAudit.model_actual_alternation => Physics.PairwisePositiveQqueAudit.model_actual_alternation,
  GUT.PairwisePositiveQqueAudit.model_characters => Physics.PairwisePositiveQqueAudit.model_characters,
  GUT.PairwisePositiveQqueAudit.model_exterior_nonzero => Physics.PairwisePositiveQqueAudit.model_exterior_nonzero,
  GUT.PairwisePositiveQqueAudit.no_three_way_support => Physics.PairwisePositiveQqueAudit.no_three_way_support,
  GUT.PairwisePositiveQqueAudit.pairwise_support => Physics.PairwisePositiveQqueAudit.pairwise_support,
  GUT.PairwisePositiveQqueAudit.profiles => Physics.PairwisePositiveQqueAudit.profiles,
  GUT.PairwisePositiveQqueAudit.profiles.eq_1 => Physics.PairwisePositiveQqueAudit.profiles.eq_1,
  GUT.PairwisePositiveQqueAudit.qr => Physics.PairwisePositiveQqueAudit.qr,
  GUT.PairwisePositiveQqueAudit.qs => Physics.PairwisePositiveQqueAudit.qs,
  GUT.PairwisePositiveQqueAudit.ur => Physics.PairwisePositiveQqueAudit.ur
]

assert_compatible GUT.PairwisePositiveQqueAudit.distinct_quotients => Physics.PairwisePositiveQqueAudit.distinct_quotients
assert_compatible GUT.PairwisePositiveQqueAudit.es => Physics.PairwisePositiveQqueAudit.es
assert_compatible GUT.PairwisePositiveQqueAudit.instAddCommGroupQuark => Physics.PairwisePositiveQqueAudit.instAddCommGroupQuark
assert_compatible GUT.PairwisePositiveQqueAudit.missingElectron => Physics.PairwisePositiveQqueAudit.missingElectron
assert_compatible GUT.PairwisePositiveQqueAudit.missing_pair => Physics.PairwisePositiveQqueAudit.missing_pair
assert_compatible GUT.PairwisePositiveQqueAudit.model_actual_alternation => Physics.PairwisePositiveQqueAudit.model_actual_alternation
assert_compatible GUT.PairwisePositiveQqueAudit.model_characters => Physics.PairwisePositiveQqueAudit.model_characters
assert_compatible GUT.PairwisePositiveQqueAudit.model_exterior_nonzero => Physics.PairwisePositiveQqueAudit.model_exterior_nonzero
assert_compatible GUT.PairwisePositiveQqueAudit.no_three_way_support => Physics.PairwisePositiveQqueAudit.no_three_way_support
assert_compatible GUT.PairwisePositiveQqueAudit.pairwise_support => Physics.PairwisePositiveQqueAudit.pairwise_support
assert_compatible GUT.PairwisePositiveQqueAudit.profiles => Physics.PairwisePositiveQqueAudit.profiles
assert_compatible GUT.PairwisePositiveQqueAudit.profiles.eq_1 => Physics.PairwisePositiveQqueAudit.profiles.eq_1
assert_compatible GUT.PairwisePositiveQqueAudit.qr => Physics.PairwisePositiveQqueAudit.qr
assert_compatible GUT.PairwisePositiveQqueAudit.qs => Physics.PairwisePositiveQqueAudit.qs
assert_compatible GUT.PairwisePositiveQqueAudit.ur => Physics.PairwisePositiveQqueAudit.ur
