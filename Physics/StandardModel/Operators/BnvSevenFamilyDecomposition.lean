import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFamilyDecomposition
import Physics.StandardModel.Operators.BnvSevenPatternDescent
import Physics.StandardModel.Operators.DeltaLOneFourFamilyDecomposition
import Math.RepresentationTheory.MixedSingleSpeciesPartition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFamilyDecomposition instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvBoundedSpecies.SevenFamily.eq_1 => Physics.BnvBoundedSpecies.SevenFamily.eq_1,
  GUT.BnvSevenFamilyDecomposition.FamilySector => Physics.BnvSevenFamilyDecomposition.FamilySector,
  GUT.BnvSevenFamilyDecomposition.OrderedSector => Physics.BnvSevenFamilyDecomposition.OrderedSector,
  GUT.BnvSevenFamilyDecomposition.counts_pattern => Physics.BnvSevenFamilyDecomposition.counts_pattern,
  GUT.BnvSevenFamilyDecomposition.disjoint => Physics.BnvSevenFamilyDecomposition.disjoint,
  GUT.BnvSevenFamilyDecomposition.equiv => Physics.BnvSevenFamilyDecomposition.equiv,
  GUT.BnvSevenFamilyDecomposition.familyCounts => Physics.BnvSevenFamilyDecomposition.familyCounts,
  GUT.BnvSevenFamilyDecomposition.familyCounts.eq_1 => Physics.BnvSevenFamilyDecomposition.familyCounts.eq_1,
  GUT.BnvSevenFamilyDecomposition.familyEquiv => Physics.BnvSevenFamilyDecomposition.familyEquiv,
  GUT.BnvSevenFamilyDecomposition.familySpace_eq => Physics.BnvSevenFamilyDecomposition.familySpace_eq,
  GUT.BnvSevenFamilyDecomposition.forbidden_iff => Physics.BnvSevenFamilyDecomposition.forbidden_iff,
  GUT.BnvSevenFamilyDecomposition.instDecidablePredScalarSpeciesSupport => Physics.BnvSevenFamilyDecomposition.instDecidablePredScalarSpeciesSupport,
  GUT.BnvSevenFamilyDecomposition.nonzero_iff => Physics.BnvSevenFamilyDecomposition.nonzero_iff,
  GUT.BnvSevenFamilyDecomposition.orbit_iff => Physics.BnvSevenFamilyDecomposition.orbit_iff,
  GUT.BnvSevenFamilyDecomposition.orderedEquiv => Physics.BnvSevenFamilyDecomposition.orderedEquiv,
  GUT.BnvSevenFamilyDecomposition.pattern => Physics.BnvSevenFamilyDecomposition.pattern,
  GUT.BnvSevenFamilyDecomposition.pattern.eq_1 => Physics.BnvSevenFamilyDecomposition.pattern.eq_1,
  GUT.BnvSevenFamilyDecomposition.pattern_baryon => Physics.BnvSevenFamilyDecomposition.pattern_baryon,
  GUT.BnvSevenFamilyDecomposition.scalar => Physics.BnvSevenFamilyDecomposition.scalar,
  GUT.BnvSevenFamilyDecomposition.scalar.eq_1 => Physics.BnvSevenFamilyDecomposition.scalar.eq_1,
  GUT.BnvSevenFamilyDecomposition.sector_eq_partition => Physics.BnvSevenFamilyDecomposition.sector_eq_partition,
  GUT.BnvSevenFamilyDecomposition.single_scalar_support => Physics.BnvSevenFamilyDecomposition.single_scalar_support,
  GUT.BnvSevenFamilyDecomposition.stable => Physics.BnvSevenFamilyDecomposition.stable,
  GUT.BnvSevenFamilyDecomposition.support => Physics.BnvSevenFamilyDecomposition.support,
  GUT.BnvSevenFamilyDecomposition.support.eq_1 => Physics.BnvSevenFamilyDecomposition.support.eq_1,
  GUT.BnvSevenFamilyDecomposition.support_of_nonzero => Physics.BnvSevenFamilyDecomposition.support_of_nonzero
]

assert_compatible GUT.BnvBoundedSpecies.SevenFamily.eq_1 => Physics.BnvBoundedSpecies.SevenFamily.eq_1
assert_compatible GUT.BnvSevenFamilyDecomposition.FamilySector => Physics.BnvSevenFamilyDecomposition.FamilySector
assert_compatible GUT.BnvSevenFamilyDecomposition.OrderedSector => Physics.BnvSevenFamilyDecomposition.OrderedSector
assert_compatible GUT.BnvSevenFamilyDecomposition.counts_pattern => Physics.BnvSevenFamilyDecomposition.counts_pattern
assert_compatible GUT.BnvSevenFamilyDecomposition.disjoint => Physics.BnvSevenFamilyDecomposition.disjoint
assert_compatible GUT.BnvSevenFamilyDecomposition.equiv => Physics.BnvSevenFamilyDecomposition.equiv
assert_compatible GUT.BnvSevenFamilyDecomposition.familyCounts => Physics.BnvSevenFamilyDecomposition.familyCounts
assert_compatible GUT.BnvSevenFamilyDecomposition.familyCounts.eq_1 => Physics.BnvSevenFamilyDecomposition.familyCounts.eq_1
assert_compatible GUT.BnvSevenFamilyDecomposition.familyEquiv => Physics.BnvSevenFamilyDecomposition.familyEquiv
assert_compatible GUT.BnvSevenFamilyDecomposition.familySpace_eq => Physics.BnvSevenFamilyDecomposition.familySpace_eq
assert_compatible GUT.BnvSevenFamilyDecomposition.forbidden_iff => Physics.BnvSevenFamilyDecomposition.forbidden_iff
assert_compatible GUT.BnvSevenFamilyDecomposition.instDecidablePredScalarSpeciesSupport => Physics.BnvSevenFamilyDecomposition.instDecidablePredScalarSpeciesSupport
assert_compatible GUT.BnvSevenFamilyDecomposition.nonzero_iff => Physics.BnvSevenFamilyDecomposition.nonzero_iff
assert_compatible GUT.BnvSevenFamilyDecomposition.orbit_iff => Physics.BnvSevenFamilyDecomposition.orbit_iff
assert_compatible GUT.BnvSevenFamilyDecomposition.orderedEquiv => Physics.BnvSevenFamilyDecomposition.orderedEquiv
assert_compatible GUT.BnvSevenFamilyDecomposition.pattern => Physics.BnvSevenFamilyDecomposition.pattern
assert_compatible GUT.BnvSevenFamilyDecomposition.pattern.eq_1 => Physics.BnvSevenFamilyDecomposition.pattern.eq_1
assert_compatible GUT.BnvSevenFamilyDecomposition.pattern_baryon => Physics.BnvSevenFamilyDecomposition.pattern_baryon
assert_compatible GUT.BnvSevenFamilyDecomposition.scalar => Physics.BnvSevenFamilyDecomposition.scalar
assert_compatible GUT.BnvSevenFamilyDecomposition.scalar.eq_1 => Physics.BnvSevenFamilyDecomposition.scalar.eq_1
assert_compatible GUT.BnvSevenFamilyDecomposition.sector_eq_partition => Physics.BnvSevenFamilyDecomposition.sector_eq_partition
assert_compatible GUT.BnvSevenFamilyDecomposition.single_scalar_support => Physics.BnvSevenFamilyDecomposition.single_scalar_support
assert_compatible GUT.BnvSevenFamilyDecomposition.stable => Physics.BnvSevenFamilyDecomposition.stable
assert_compatible GUT.BnvSevenFamilyDecomposition.support => Physics.BnvSevenFamilyDecomposition.support
assert_compatible GUT.BnvSevenFamilyDecomposition.support.eq_1 => Physics.BnvSevenFamilyDecomposition.support.eq_1
assert_compatible GUT.BnvSevenFamilyDecomposition.support_of_nonzero => Physics.BnvSevenFamilyDecomposition.support_of_nonzero
