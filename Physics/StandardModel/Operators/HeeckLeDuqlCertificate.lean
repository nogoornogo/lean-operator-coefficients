import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.HeeckLeDuqlCertificate
import Physics.StandardModel.Operators.DuqlExteriorCompleteness
import Math.RepresentationTheory.InvariantFunctionalCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.HeeckLeDuqlCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeDuqlCertificate.candidate => Physics.HeeckLeDuqlCertificate.candidate,
  GUT.HeeckLeDuqlCertificate.candidate_eq => Physics.HeeckLeDuqlCertificate.candidate_eq,
  GUT.HeeckLeDuqlCertificate.candidate_extract => Physics.HeeckLeDuqlCertificate.candidate_extract,
  GUT.HeeckLeDuqlCertificate.extract_candidate => Physics.HeeckLeDuqlCertificate.extract_candidate,
  GUT.HeeckLeDuqlCertificate.finiteEquiv => Physics.HeeckLeDuqlCertificate.finiteEquiv,
  GUT.HeeckLeDuqlCertificate.finite_inverse_is_candidate => Physics.HeeckLeDuqlCertificate.finite_inverse_is_candidate,
  GUT.HeeckLeDuqlCertificate.flavorBasis => Physics.HeeckLeDuqlCertificate.flavorBasis,
  GUT.HeeckLeDuqlCertificate.flavorBasis_independent => Physics.HeeckLeDuqlCertificate.flavorBasis_independent,
  GUT.HeeckLeDuqlCertificate.flavorBasis_is_candidate => Physics.HeeckLeDuqlCertificate.flavorBasis_is_candidate,
  GUT.HeeckLeDuqlCertificate.flavorBasis_spans => Physics.HeeckLeDuqlCertificate.flavorBasis_spans,
  GUT.HeeckLeDuqlCertificate.flavorEquiv => Physics.HeeckLeDuqlCertificate.flavorEquiv,
  GUT.HeeckLeDuqlCertificate.flavor_finrank => Physics.HeeckLeDuqlCertificate.flavor_finrank,
  GUT.HeeckLeDuqlCertificate.ordered => Physics.HeeckLeDuqlCertificate.ordered,
  GUT.HeeckLeDuqlCertificate.ordered_apply => Physics.HeeckLeDuqlCertificate.ordered_apply,
  GUT.HeeckLeDuqlCertificate.ordered_eq => Physics.HeeckLeDuqlCertificate.ordered_eq,
  GUT.HeeckLeDuqlCertificate.tensorBasis => Physics.HeeckLeDuqlCertificate.tensorBasis
]

assert_compatible GUT.HeeckLeDuqlCertificate.candidate => Physics.HeeckLeDuqlCertificate.candidate
assert_compatible GUT.HeeckLeDuqlCertificate.candidate_eq => Physics.HeeckLeDuqlCertificate.candidate_eq
assert_compatible GUT.HeeckLeDuqlCertificate.candidate_extract => Physics.HeeckLeDuqlCertificate.candidate_extract
assert_compatible GUT.HeeckLeDuqlCertificate.extract_candidate => Physics.HeeckLeDuqlCertificate.extract_candidate
assert_compatible GUT.HeeckLeDuqlCertificate.finiteEquiv => Physics.HeeckLeDuqlCertificate.finiteEquiv
assert_compatible GUT.HeeckLeDuqlCertificate.finite_inverse_is_candidate => Physics.HeeckLeDuqlCertificate.finite_inverse_is_candidate
assert_compatible GUT.HeeckLeDuqlCertificate.flavorBasis => Physics.HeeckLeDuqlCertificate.flavorBasis
assert_compatible GUT.HeeckLeDuqlCertificate.flavorBasis_independent => Physics.HeeckLeDuqlCertificate.flavorBasis_independent
assert_compatible GUT.HeeckLeDuqlCertificate.flavorBasis_is_candidate => Physics.HeeckLeDuqlCertificate.flavorBasis_is_candidate
assert_compatible GUT.HeeckLeDuqlCertificate.flavorBasis_spans => Physics.HeeckLeDuqlCertificate.flavorBasis_spans
assert_compatible GUT.HeeckLeDuqlCertificate.flavorEquiv => Physics.HeeckLeDuqlCertificate.flavorEquiv
assert_compatible GUT.HeeckLeDuqlCertificate.flavor_finrank => Physics.HeeckLeDuqlCertificate.flavor_finrank
assert_compatible GUT.HeeckLeDuqlCertificate.ordered => Physics.HeeckLeDuqlCertificate.ordered
assert_compatible GUT.HeeckLeDuqlCertificate.ordered_apply => Physics.HeeckLeDuqlCertificate.ordered_apply
assert_compatible GUT.HeeckLeDuqlCertificate.ordered_eq => Physics.HeeckLeDuqlCertificate.ordered_eq
assert_compatible GUT.HeeckLeDuqlCertificate.tensorBasis => Physics.HeeckLeDuqlCertificate.tensorBasis
