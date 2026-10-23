import Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlExterior
import Physics.StandardModel.Operators.LiQqqlConvention
import Physics.StandardModel.Operators.QqqlFiniteFlavor
import Math.RepresentationTheory.FourSlotTripleOrbit
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlExterior instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiQqqlExterior.candidate => Physics.LiQqqlExterior.candidate,
  GUT.LiQqqlExterior.candidate_eq => Physics.LiQqqlExterior.candidate_eq,
  GUT.LiQqqlExterior.candidate_injective => Physics.LiQqqlExterior.candidate_injective,
  GUT.LiQqqlExterior.evaluate_orbit => Physics.LiQqqlExterior.evaluate_orbit,
  GUT.LiQqqlExterior.every_sector_is_candidate => Physics.LiQqqlExterior.every_sector_is_candidate,
  GUT.LiQqqlExterior.instAddCommGroupTensorProductComplexColorWeakSpace => Physics.LiQqqlExterior.instAddCommGroupTensorProductComplexColorWeakSpace,
  GUT.LiQqqlExterior.instAddCommGroupTensorProductComplexWeakSpace => Physics.LiQqqlExterior.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.LiQqqlExterior.orderedSeed => Physics.LiQqqlExterior.orderedSeed,
  GUT.LiQqqlExterior.orderedSeed_apply => Physics.LiQqqlExterior.orderedSeed_apply,
  GUT.LiQqqlExterior.restriction_candidate => Physics.LiQqqlExterior.restriction_candidate,
  GUT.LiQqqlExterior.seedFamily => Physics.LiQqqlExterior.seedFamily,
  GUT.LiQqqlExterior.seedFamily.eq_1 => Physics.LiQqqlExterior.seedFamily.eq_1
]

assert_compatible GUT.LiQqqlExterior.candidate => Physics.LiQqqlExterior.candidate
assert_compatible GUT.LiQqqlExterior.candidate_eq => Physics.LiQqqlExterior.candidate_eq
assert_compatible GUT.LiQqqlExterior.candidate_injective => Physics.LiQqqlExterior.candidate_injective
assert_compatible GUT.LiQqqlExterior.evaluate_orbit => Physics.LiQqqlExterior.evaluate_orbit
assert_compatible GUT.LiQqqlExterior.every_sector_is_candidate => Physics.LiQqqlExterior.every_sector_is_candidate
assert_compatible GUT.LiQqqlExterior.instAddCommGroupTensorProductComplexColorWeakSpace => Physics.LiQqqlExterior.instAddCommGroupTensorProductComplexColorWeakSpace
assert_compatible GUT.LiQqqlExterior.instAddCommGroupTensorProductComplexWeakSpace => Physics.LiQqqlExterior.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.LiQqqlExterior.orderedSeed => Physics.LiQqqlExterior.orderedSeed
assert_compatible GUT.LiQqqlExterior.orderedSeed_apply => Physics.LiQqqlExterior.orderedSeed_apply
assert_compatible GUT.LiQqqlExterior.restriction_candidate => Physics.LiQqqlExterior.restriction_candidate
assert_compatible GUT.LiQqqlExterior.seedFamily => Physics.LiQqqlExterior.seedFamily
assert_compatible GUT.LiQqqlExterior.seedFamily.eq_1 => Physics.LiQqqlExterior.seedFamily.eq_1
