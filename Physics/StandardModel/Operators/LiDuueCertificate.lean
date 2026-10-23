import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueCertificate
import Physics.StandardModel.Operators.LiDuueConvention
import Math.RepresentationTheory.InvariantFunctionalCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuueResidualCompleteness.complete.eq_1 => Physics.DuueResidualCompleteness.complete.eq_1,
  GUT.LiDuueCertificate.candidate => Physics.LiDuueCertificate.candidate,
  GUT.LiDuueCertificate.candidate_eq => Physics.LiDuueCertificate.candidate_eq,
  GUT.LiDuueCertificate.candidate_extract => Physics.LiDuueCertificate.candidate_extract,
  GUT.LiDuueCertificate.extract_candidate => Physics.LiDuueCertificate.extract_candidate,
  GUT.LiDuueCertificate.finiteEquiv => Physics.LiDuueCertificate.finiteEquiv,
  GUT.LiDuueCertificate.finite_inverse_is_candidate => Physics.LiDuueCertificate.finite_inverse_is_candidate,
  GUT.LiDuueCertificate.flavorBasis => Physics.LiDuueCertificate.flavorBasis,
  GUT.LiDuueCertificate.flavorBasis_independent => Physics.LiDuueCertificate.flavorBasis_independent,
  GUT.LiDuueCertificate.flavorBasis_is_candidate => Physics.LiDuueCertificate.flavorBasis_is_candidate,
  GUT.LiDuueCertificate.flavorBasis_spans => Physics.LiDuueCertificate.flavorBasis_spans,
  GUT.LiDuueCertificate.flavorEquiv => Physics.LiDuueCertificate.flavorEquiv,
  GUT.LiDuueCertificate.flavor_finrank => Physics.LiDuueCertificate.flavor_finrank,
  GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace,
  GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace_1 => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace_1,
  GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexSpace => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexSpace,
  GUT.LiDuueCertificate.ordered => Physics.LiDuueCertificate.ordered,
  GUT.LiDuueCertificate.ordered.eq_1 => Physics.LiDuueCertificate.ordered.eq_1,
  GUT.LiDuueCertificate.ordered_apply => Physics.LiDuueCertificate.ordered_apply,
  GUT.LiDuueCertificate.restriction_candidate => Physics.LiDuueCertificate.restriction_candidate,
  GUT.LiDuueCertificate.seedCoordinates => Physics.LiDuueCertificate.seedCoordinates,
  GUT.LiDuueCertificate.seedCoordinates.eq_1 => Physics.LiDuueCertificate.seedCoordinates.eq_1,
  GUT.LiDuueCertificate.tensorBasis => Physics.LiDuueCertificate.tensorBasis
]

assert_compatible GUT.DuueResidualCompleteness.complete.eq_1 => Physics.DuueResidualCompleteness.complete.eq_1
assert_compatible GUT.LiDuueCertificate.candidate => Physics.LiDuueCertificate.candidate
assert_compatible GUT.LiDuueCertificate.candidate_eq => Physics.LiDuueCertificate.candidate_eq
assert_compatible GUT.LiDuueCertificate.candidate_extract => Physics.LiDuueCertificate.candidate_extract
assert_compatible GUT.LiDuueCertificate.extract_candidate => Physics.LiDuueCertificate.extract_candidate
assert_compatible GUT.LiDuueCertificate.finiteEquiv => Physics.LiDuueCertificate.finiteEquiv
assert_compatible GUT.LiDuueCertificate.finite_inverse_is_candidate => Physics.LiDuueCertificate.finite_inverse_is_candidate
assert_compatible GUT.LiDuueCertificate.flavorBasis => Physics.LiDuueCertificate.flavorBasis
assert_compatible GUT.LiDuueCertificate.flavorBasis_independent => Physics.LiDuueCertificate.flavorBasis_independent
assert_compatible GUT.LiDuueCertificate.flavorBasis_is_candidate => Physics.LiDuueCertificate.flavorBasis_is_candidate
assert_compatible GUT.LiDuueCertificate.flavorBasis_spans => Physics.LiDuueCertificate.flavorBasis_spans
assert_compatible GUT.LiDuueCertificate.flavorEquiv => Physics.LiDuueCertificate.flavorEquiv
assert_compatible GUT.LiDuueCertificate.flavor_finrank => Physics.LiDuueCertificate.flavor_finrank
assert_compatible GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace
assert_compatible GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace_1 => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexColorSpace_1
assert_compatible GUT.LiDuueCertificate.instAddCommGroupTensorProductComplexSpace => Physics.LiDuueCertificate.instAddCommGroupTensorProductComplexSpace
assert_compatible GUT.LiDuueCertificate.ordered => Physics.LiDuueCertificate.ordered
assert_compatible GUT.LiDuueCertificate.ordered.eq_1 => Physics.LiDuueCertificate.ordered.eq_1
assert_compatible GUT.LiDuueCertificate.ordered_apply => Physics.LiDuueCertificate.ordered_apply
assert_compatible GUT.LiDuueCertificate.restriction_candidate => Physics.LiDuueCertificate.restriction_candidate
assert_compatible GUT.LiDuueCertificate.seedCoordinates => Physics.LiDuueCertificate.seedCoordinates
assert_compatible GUT.LiDuueCertificate.seedCoordinates.eq_1 => Physics.LiDuueCertificate.seedCoordinates.eq_1
assert_compatible GUT.LiDuueCertificate.tensorBasis => Physics.LiDuueCertificate.tensorBasis
