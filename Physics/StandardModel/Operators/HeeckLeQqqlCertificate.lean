import Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlCertificate
import Physics.StandardModel.Operators.HeeckLeQqqlConvention
import Physics.StandardModel.Operators.QqqlFiniteFlavor
import Math.RepresentationTheory.FourSlotTripleOrbit
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeQqqlCertificate.candidate => Physics.HeeckLeQqqlCertificate.candidate,
  GUT.HeeckLeQqqlCertificate.candidate_eq => Physics.HeeckLeQqqlCertificate.candidate_eq,
  GUT.HeeckLeQqqlCertificate.candidate_injective => Physics.HeeckLeQqqlCertificate.candidate_injective,
  GUT.HeeckLeQqqlCertificate.evaluate_orbit => Physics.HeeckLeQqqlCertificate.evaluate_orbit,
  GUT.HeeckLeQqqlCertificate.every_sector_is_candidate => Physics.HeeckLeQqqlCertificate.every_sector_is_candidate,
  GUT.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexColorWeakSpace => Physics.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexColorWeakSpace,
  GUT.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexWeakSpace => Physics.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.HeeckLeQqqlCertificate.orderedSeed => Physics.HeeckLeQqqlCertificate.orderedSeed,
  GUT.HeeckLeQqqlCertificate.orderedSeed_apply => Physics.HeeckLeQqqlCertificate.orderedSeed_apply,
  GUT.HeeckLeQqqlCertificate.restriction_candidate => Physics.HeeckLeQqqlCertificate.restriction_candidate,
  GUT.HeeckLeQqqlCertificate.seedFamily => Physics.HeeckLeQqqlCertificate.seedFamily,
  GUT.HeeckLeQqqlCertificate.seedFamily.eq_1 => Physics.HeeckLeQqqlCertificate.seedFamily.eq_1
]

assert_compatible GUT.HeeckLeQqqlCertificate.candidate => Physics.HeeckLeQqqlCertificate.candidate
assert_compatible GUT.HeeckLeQqqlCertificate.candidate_eq => Physics.HeeckLeQqqlCertificate.candidate_eq
assert_compatible GUT.HeeckLeQqqlCertificate.candidate_injective => Physics.HeeckLeQqqlCertificate.candidate_injective
assert_compatible GUT.HeeckLeQqqlCertificate.evaluate_orbit => Physics.HeeckLeQqqlCertificate.evaluate_orbit
assert_compatible GUT.HeeckLeQqqlCertificate.every_sector_is_candidate => Physics.HeeckLeQqqlCertificate.every_sector_is_candidate
assert_compatible GUT.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexColorWeakSpace => Physics.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexColorWeakSpace
assert_compatible GUT.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexWeakSpace => Physics.HeeckLeQqqlCertificate.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.HeeckLeQqqlCertificate.orderedSeed => Physics.HeeckLeQqqlCertificate.orderedSeed
assert_compatible GUT.HeeckLeQqqlCertificate.orderedSeed_apply => Physics.HeeckLeQqqlCertificate.orderedSeed_apply
assert_compatible GUT.HeeckLeQqqlCertificate.restriction_candidate => Physics.HeeckLeQqqlCertificate.restriction_candidate
assert_compatible GUT.HeeckLeQqqlCertificate.seedFamily => Physics.HeeckLeQqqlCertificate.seedFamily
assert_compatible GUT.HeeckLeQqqlCertificate.seedFamily.eq_1 => Physics.HeeckLeQqqlCertificate.seedFamily.eq_1
