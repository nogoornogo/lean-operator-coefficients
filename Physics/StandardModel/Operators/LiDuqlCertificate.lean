import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlCertificate
import Physics.StandardModel.Operators.LiDuqlConvention
import Math.RepresentationTheory.InvariantFunctionalCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiDuqlCertificate.candidate => Physics.LiDuqlCertificate.candidate,
  GUT.LiDuqlCertificate.candidate_eq => Physics.LiDuqlCertificate.candidate_eq,
  GUT.LiDuqlCertificate.candidate_extract => Physics.LiDuqlCertificate.candidate_extract,
  GUT.LiDuqlCertificate.extract_candidate => Physics.LiDuqlCertificate.extract_candidate,
  GUT.LiDuqlCertificate.finiteEquiv => Physics.LiDuqlCertificate.finiteEquiv,
  GUT.LiDuqlCertificate.finite_inverse_is_candidate => Physics.LiDuqlCertificate.finite_inverse_is_candidate,
  GUT.LiDuqlCertificate.flavorBasis => Physics.LiDuqlCertificate.flavorBasis,
  GUT.LiDuqlCertificate.flavorBasis_independent => Physics.LiDuqlCertificate.flavorBasis_independent,
  GUT.LiDuqlCertificate.flavorBasis_is_candidate => Physics.LiDuqlCertificate.flavorBasis_is_candidate,
  GUT.LiDuqlCertificate.flavorBasis_spans => Physics.LiDuqlCertificate.flavorBasis_spans,
  GUT.LiDuqlCertificate.flavorEquiv => Physics.LiDuqlCertificate.flavorEquiv,
  GUT.LiDuqlCertificate.flavor_finrank => Physics.LiDuqlCertificate.flavor_finrank,
  GUT.LiDuqlCertificate.ordered => Physics.LiDuqlCertificate.ordered,
  GUT.LiDuqlCertificate.ordered_apply => Physics.LiDuqlCertificate.ordered_apply,
  GUT.LiDuqlCertificate.ordered_eq => Physics.LiDuqlCertificate.ordered_eq,
  GUT.LiDuqlCertificate.tensorBasis => Physics.LiDuqlCertificate.tensorBasis
]

assert_compatible GUT.LiDuqlCertificate.candidate => Physics.LiDuqlCertificate.candidate
assert_compatible GUT.LiDuqlCertificate.candidate_eq => Physics.LiDuqlCertificate.candidate_eq
assert_compatible GUT.LiDuqlCertificate.candidate_extract => Physics.LiDuqlCertificate.candidate_extract
assert_compatible GUT.LiDuqlCertificate.extract_candidate => Physics.LiDuqlCertificate.extract_candidate
assert_compatible GUT.LiDuqlCertificate.finiteEquiv => Physics.LiDuqlCertificate.finiteEquiv
assert_compatible GUT.LiDuqlCertificate.finite_inverse_is_candidate => Physics.LiDuqlCertificate.finite_inverse_is_candidate
assert_compatible GUT.LiDuqlCertificate.flavorBasis => Physics.LiDuqlCertificate.flavorBasis
assert_compatible GUT.LiDuqlCertificate.flavorBasis_independent => Physics.LiDuqlCertificate.flavorBasis_independent
assert_compatible GUT.LiDuqlCertificate.flavorBasis_is_candidate => Physics.LiDuqlCertificate.flavorBasis_is_candidate
assert_compatible GUT.LiDuqlCertificate.flavorBasis_spans => Physics.LiDuqlCertificate.flavorBasis_spans
assert_compatible GUT.LiDuqlCertificate.flavorEquiv => Physics.LiDuqlCertificate.flavorEquiv
assert_compatible GUT.LiDuqlCertificate.flavor_finrank => Physics.LiDuqlCertificate.flavor_finrank
assert_compatible GUT.LiDuqlCertificate.ordered => Physics.LiDuqlCertificate.ordered
assert_compatible GUT.LiDuqlCertificate.ordered_apply => Physics.LiDuqlCertificate.ordered_apply
assert_compatible GUT.LiDuqlCertificate.ordered_eq => Physics.LiDuqlCertificate.ordered_eq
assert_compatible GUT.LiDuqlCertificate.tensorBasis => Physics.LiDuqlCertificate.tensorBasis
