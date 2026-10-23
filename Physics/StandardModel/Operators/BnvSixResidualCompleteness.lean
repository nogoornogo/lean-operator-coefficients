import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSixResidualCompleteness
import Physics.StandardModel.Operators.BnvSignedFieldTransport
import Physics.StandardModel.Operators.BnvZeroBosonBridge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSixResidualCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSixResidualCompleteness.ResidualProduct => Physics.BnvSixResidualCompleteness.ResidualProduct,
  GUT.BnvSixResidualCompleteness.baryon_opposite => Physics.BnvSixResidualCompleteness.baryon_opposite,
  GUT.BnvSixResidualCompleteness.degree => Physics.BnvSixResidualCompleteness.degree,
  GUT.BnvSixResidualCompleteness.degree.eq_1 => Physics.BnvSixResidualCompleteness.degree.eq_1,
  GUT.BnvSixResidualCompleteness.disjoint => Physics.BnvSixResidualCompleteness.disjoint,
  GUT.BnvSixResidualCompleteness.equiv => Physics.BnvSixResidualCompleteness.equiv,
  GUT.BnvSixResidualCompleteness.forbidden_iff => Physics.BnvSixResidualCompleteness.forbidden_iff,
  GUT.BnvSixResidualCompleteness.instDecidablePredForallFinOfNatNatSpeciesSupport => Physics.BnvSixResidualCompleteness.instDecidablePredForallFinOfNatNatSpeciesSupport,
  GUT.BnvSixResidualCompleteness.negative_bnv => Physics.BnvSixResidualCompleteness.negative_bnv,
  GUT.BnvSixResidualCompleteness.positive_bnv => Physics.BnvSixResidualCompleteness.positive_bnv,
  GUT.BnvSixResidualCompleteness.sectorProduct => Physics.BnvSixResidualCompleteness.sectorProduct,
  GUT.BnvSixResidualCompleteness.sector_bnv => Physics.BnvSixResidualCompleteness.sector_bnv,
  GUT.BnvSixResidualCompleteness.signed_eq_partition => Physics.BnvSixResidualCompleteness.signed_eq_partition,
  GUT.BnvSixResidualCompleteness.stable => Physics.BnvSixResidualCompleteness.stable,
  GUT.BnvSixResidualCompleteness.support => Physics.BnvSixResidualCompleteness.support,
  GUT.BnvSixResidualCompleteness.support.eq_1 => Physics.BnvSixResidualCompleteness.support.eq_1,
  GUT.BnvSixResidualCompleteness.support_eq_sector => Physics.BnvSixResidualCompleteness.support_eq_sector
]

assert_compatible GUT.BnvSixResidualCompleteness.ResidualProduct => Physics.BnvSixResidualCompleteness.ResidualProduct
assert_compatible GUT.BnvSixResidualCompleteness.baryon_opposite => Physics.BnvSixResidualCompleteness.baryon_opposite
assert_compatible GUT.BnvSixResidualCompleteness.degree => Physics.BnvSixResidualCompleteness.degree
assert_compatible GUT.BnvSixResidualCompleteness.degree.eq_1 => Physics.BnvSixResidualCompleteness.degree.eq_1
assert_compatible GUT.BnvSixResidualCompleteness.disjoint => Physics.BnvSixResidualCompleteness.disjoint
assert_compatible GUT.BnvSixResidualCompleteness.equiv => Physics.BnvSixResidualCompleteness.equiv
assert_compatible GUT.BnvSixResidualCompleteness.forbidden_iff => Physics.BnvSixResidualCompleteness.forbidden_iff
assert_compatible GUT.BnvSixResidualCompleteness.instDecidablePredForallFinOfNatNatSpeciesSupport => Physics.BnvSixResidualCompleteness.instDecidablePredForallFinOfNatNatSpeciesSupport
assert_compatible GUT.BnvSixResidualCompleteness.negative_bnv => Physics.BnvSixResidualCompleteness.negative_bnv
assert_compatible GUT.BnvSixResidualCompleteness.positive_bnv => Physics.BnvSixResidualCompleteness.positive_bnv
assert_compatible GUT.BnvSixResidualCompleteness.sectorProduct => Physics.BnvSixResidualCompleteness.sectorProduct
assert_compatible GUT.BnvSixResidualCompleteness.sector_bnv => Physics.BnvSixResidualCompleteness.sector_bnv
assert_compatible GUT.BnvSixResidualCompleteness.signed_eq_partition => Physics.BnvSixResidualCompleteness.signed_eq_partition
assert_compatible GUT.BnvSixResidualCompleteness.stable => Physics.BnvSixResidualCompleteness.stable
assert_compatible GUT.BnvSixResidualCompleteness.support => Physics.BnvSixResidualCompleteness.support
assert_compatible GUT.BnvSixResidualCompleteness.support.eq_1 => Physics.BnvSixResidualCompleteness.support.eq_1
assert_compatible GUT.BnvSixResidualCompleteness.support_eq_sector => Physics.BnvSixResidualCompleteness.support_eq_sector
