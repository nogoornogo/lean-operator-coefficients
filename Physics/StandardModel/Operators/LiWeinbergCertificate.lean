import Physics.StandardModel.Operators.Weinberg.LiWeinbergCertificate
import Physics.StandardModel.Operators.WeinbergSMInterface
import Physics.StandardModel.Operators.LiWeinbergConvention
import Math.RepresentationTheory.InvariantFunctionalCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.LiWeinbergCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiWeinbergCertificate.Residual => Physics.LiWeinbergCertificate.Residual,
  GUT.LiWeinbergCertificate.candidate => Physics.LiWeinbergCertificate.candidate,
  GUT.LiWeinbergCertificate.candidate_apply => Physics.LiWeinbergCertificate.candidate_apply,
  GUT.LiWeinbergCertificate.candidate_diagonal => Physics.LiWeinbergCertificate.candidate_diagonal,
  GUT.LiWeinbergCertificate.candidate_eq => Physics.LiWeinbergCertificate.candidate_eq,
  GUT.LiWeinbergCertificate.candidate_extract => Physics.LiWeinbergCertificate.candidate_extract,
  GUT.LiWeinbergCertificate.extract_candidate => Physics.LiWeinbergCertificate.extract_candidate,
  GUT.LiWeinbergCertificate.finiteEquiv => Physics.LiWeinbergCertificate.finiteEquiv,
  GUT.LiWeinbergCertificate.finite_inverse_is_candidate => Physics.LiWeinbergCertificate.finite_inverse_is_candidate,
  GUT.LiWeinbergCertificate.finite_trivial_finrank => Physics.LiWeinbergCertificate.finite_trivial_finrank,
  GUT.LiWeinbergCertificate.flavorBasis => Physics.LiWeinbergCertificate.flavorBasis,
  GUT.LiWeinbergCertificate.flavorBasis_independent => Physics.LiWeinbergCertificate.flavorBasis_independent,
  GUT.LiWeinbergCertificate.flavorBasis_is_candidate => Physics.LiWeinbergCertificate.flavorBasis_is_candidate,
  GUT.LiWeinbergCertificate.flavorBasis_spans => Physics.LiWeinbergCertificate.flavorBasis_spans,
  GUT.LiWeinbergCertificate.flavorEquiv => Physics.LiWeinbergCertificate.flavorEquiv,
  GUT.LiWeinbergCertificate.flavor_entry => Physics.LiWeinbergCertificate.flavor_entry,
  GUT.LiWeinbergCertificate.flavor_finrank => Physics.LiWeinbergCertificate.flavor_finrank,
  GUT.LiWeinbergCertificate.mass_formula => Physics.LiWeinbergCertificate.mass_formula,
  GUT.LiWeinbergCertificate.onFieldsCandidate => Physics.LiWeinbergCertificate.onFieldsCandidate,
  GUT.LiWeinbergCertificate.onFields_extract => Physics.LiWeinbergCertificate.onFields_extract,
  GUT.LiWeinbergCertificate.onFields_reconstruct => Physics.LiWeinbergCertificate.onFields_reconstruct,
  GUT.LiWeinbergCertificate.ordered => Physics.LiWeinbergCertificate.ordered,
  GUT.LiWeinbergCertificate.ordered_eq => Physics.LiWeinbergCertificate.ordered_eq,
  GUT.LiWeinbergCertificate.probe => Physics.LiWeinbergCertificate.probe,
  GUT.LiWeinbergCertificate.sign_candidate_nonzero => Physics.LiWeinbergCertificate.sign_candidate_nonzero,
  GUT.LiWeinbergCertificate.trivial_symmetric_action => Physics.LiWeinbergCertificate.trivial_symmetric_action,
  GUT.WeinbergResidualHom.homEquiv.eq_1 => Physics.WeinbergResidualHom.homEquiv.eq_1,
  GUT.WeinbergSMInterface.homEquiv.eq_1 => Physics.WeinbergSMInterface.homEquiv.eq_1
]

assert_compatible GUT.LiWeinbergCertificate.Residual => Physics.LiWeinbergCertificate.Residual
assert_compatible GUT.LiWeinbergCertificate.candidate => Physics.LiWeinbergCertificate.candidate
assert_compatible GUT.LiWeinbergCertificate.candidate_apply => Physics.LiWeinbergCertificate.candidate_apply
assert_compatible GUT.LiWeinbergCertificate.candidate_diagonal => Physics.LiWeinbergCertificate.candidate_diagonal
assert_compatible GUT.LiWeinbergCertificate.candidate_eq => Physics.LiWeinbergCertificate.candidate_eq
assert_compatible GUT.LiWeinbergCertificate.candidate_extract => Physics.LiWeinbergCertificate.candidate_extract
assert_compatible GUT.LiWeinbergCertificate.extract_candidate => Physics.LiWeinbergCertificate.extract_candidate
assert_compatible GUT.LiWeinbergCertificate.finiteEquiv => Physics.LiWeinbergCertificate.finiteEquiv
assert_compatible GUT.LiWeinbergCertificate.finite_inverse_is_candidate => Physics.LiWeinbergCertificate.finite_inverse_is_candidate
assert_compatible GUT.LiWeinbergCertificate.finite_trivial_finrank => Physics.LiWeinbergCertificate.finite_trivial_finrank
assert_compatible GUT.LiWeinbergCertificate.flavorBasis => Physics.LiWeinbergCertificate.flavorBasis
assert_compatible GUT.LiWeinbergCertificate.flavorBasis_independent => Physics.LiWeinbergCertificate.flavorBasis_independent
assert_compatible GUT.LiWeinbergCertificate.flavorBasis_is_candidate => Physics.LiWeinbergCertificate.flavorBasis_is_candidate
assert_compatible GUT.LiWeinbergCertificate.flavorBasis_spans => Physics.LiWeinbergCertificate.flavorBasis_spans
assert_compatible GUT.LiWeinbergCertificate.flavorEquiv => Physics.LiWeinbergCertificate.flavorEquiv
assert_compatible GUT.LiWeinbergCertificate.flavor_entry => Physics.LiWeinbergCertificate.flavor_entry
assert_compatible GUT.LiWeinbergCertificate.flavor_finrank => Physics.LiWeinbergCertificate.flavor_finrank
assert_compatible GUT.LiWeinbergCertificate.mass_formula => Physics.LiWeinbergCertificate.mass_formula
assert_compatible GUT.LiWeinbergCertificate.onFieldsCandidate => Physics.LiWeinbergCertificate.onFieldsCandidate
assert_compatible GUT.LiWeinbergCertificate.onFields_extract => Physics.LiWeinbergCertificate.onFields_extract
assert_compatible GUT.LiWeinbergCertificate.onFields_reconstruct => Physics.LiWeinbergCertificate.onFields_reconstruct
assert_compatible GUT.LiWeinbergCertificate.ordered => Physics.LiWeinbergCertificate.ordered
assert_compatible GUT.LiWeinbergCertificate.ordered_eq => Physics.LiWeinbergCertificate.ordered_eq
assert_compatible GUT.LiWeinbergCertificate.probe => Physics.LiWeinbergCertificate.probe
assert_compatible GUT.LiWeinbergCertificate.sign_candidate_nonzero => Physics.LiWeinbergCertificate.sign_candidate_nonzero
assert_compatible GUT.LiWeinbergCertificate.trivial_symmetric_action => Physics.LiWeinbergCertificate.trivial_symmetric_action
assert_compatible GUT.WeinbergResidualHom.homEquiv.eq_1 => Physics.WeinbergResidualHom.homEquiv.eq_1
assert_compatible GUT.WeinbergSMInterface.homEquiv.eq_1 => Physics.WeinbergSMInterface.homEquiv.eq_1
