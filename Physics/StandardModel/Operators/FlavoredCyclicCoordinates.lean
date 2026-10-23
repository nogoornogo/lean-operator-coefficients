import Physics.StandardModel.Operators.Selection.FlavoredCyclicCoordinates
import Math.RepresentationTheory.CyclicWeightCoordinates
import Math.RepresentationTheory.SymmetricTensorFunctional
import Physics.StandardModel.Operators.LiWeinbergCertificate
import Physics.StandardModel.Operators.LiDuqlCertificate
import Physics.StandardModel.Operators.LiDuueCertificate
import Physics.StandardModel.Operators.QquePhysicalExteriorCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.FlavoredCyclicCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavoredCyclicCoordinates.duqlEquiv => Physics.FlavoredCyclicCoordinates.duqlEquiv,
  GUT.FlavoredCyclicCoordinates.duql_allowed => Physics.FlavoredCyclicCoordinates.duql_allowed,
  GUT.FlavoredCyclicCoordinates.duql_finrank => Physics.FlavoredCyclicCoordinates.duql_finrank,
  GUT.FlavoredCyclicCoordinates.duql_forbidden => Physics.FlavoredCyclicCoordinates.duql_forbidden,
  GUT.FlavoredCyclicCoordinates.duueEquiv => Physics.FlavoredCyclicCoordinates.duueEquiv,
  GUT.FlavoredCyclicCoordinates.duue_allowed => Physics.FlavoredCyclicCoordinates.duue_allowed,
  GUT.FlavoredCyclicCoordinates.duue_finrank => Physics.FlavoredCyclicCoordinates.duue_finrank,
  GUT.FlavoredCyclicCoordinates.duue_forbidden => Physics.FlavoredCyclicCoordinates.duue_forbidden,
  GUT.FlavoredCyclicCoordinates.fourBasis => Physics.FlavoredCyclicCoordinates.fourBasis,
  GUT.FlavoredCyclicCoordinates.fourBasis.eq_1 => Physics.FlavoredCyclicCoordinates.fourBasis.eq_1,
  GUT.FlavoredCyclicCoordinates.fourCharge => Physics.FlavoredCyclicCoordinates.fourCharge,
  GUT.FlavoredCyclicCoordinates.fourCharge.eq_1 => Physics.FlavoredCyclicCoordinates.fourCharge.eq_1,
  GUT.FlavoredCyclicCoordinates.four_weights => Physics.FlavoredCyclicCoordinates.four_weights,
  GUT.FlavoredCyclicCoordinates.llhhEquiv => Physics.FlavoredCyclicCoordinates.llhhEquiv,
  GUT.FlavoredCyclicCoordinates.llhh_allowed => Physics.FlavoredCyclicCoordinates.llhh_allowed,
  GUT.FlavoredCyclicCoordinates.llhh_finrank => Physics.FlavoredCyclicCoordinates.llhh_finrank,
  GUT.FlavoredCyclicCoordinates.llhh_forbidden => Physics.FlavoredCyclicCoordinates.llhh_forbidden,
  GUT.FlavoredCyclicCoordinates.qqueBasis => Physics.FlavoredCyclicCoordinates.qqueBasis,
  GUT.FlavoredCyclicCoordinates.qqueBasis.eq_1 => Physics.FlavoredCyclicCoordinates.qqueBasis.eq_1,
  GUT.FlavoredCyclicCoordinates.qqueCharge => Physics.FlavoredCyclicCoordinates.qqueCharge,
  GUT.FlavoredCyclicCoordinates.qqueCharge.eq_1 => Physics.FlavoredCyclicCoordinates.qqueCharge.eq_1,
  GUT.FlavoredCyclicCoordinates.qqueEquiv => Physics.FlavoredCyclicCoordinates.qqueEquiv,
  GUT.FlavoredCyclicCoordinates.qqueHomEquiv => Physics.FlavoredCyclicCoordinates.qqueHomEquiv,
  GUT.FlavoredCyclicCoordinates.qqueSymmetricEquiv => Physics.FlavoredCyclicCoordinates.qqueSymmetricEquiv,
  GUT.FlavoredCyclicCoordinates.qque_allowed => Physics.FlavoredCyclicCoordinates.qque_allowed,
  GUT.FlavoredCyclicCoordinates.qque_finrank => Physics.FlavoredCyclicCoordinates.qque_finrank,
  GUT.FlavoredCyclicCoordinates.qque_forbidden => Physics.FlavoredCyclicCoordinates.qque_forbidden,
  GUT.FlavoredCyclicCoordinates.qque_weights => Physics.FlavoredCyclicCoordinates.qque_weights
]

assert_compatible GUT.FlavoredCyclicCoordinates.duqlEquiv => Physics.FlavoredCyclicCoordinates.duqlEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.duql_allowed => Physics.FlavoredCyclicCoordinates.duql_allowed
assert_compatible GUT.FlavoredCyclicCoordinates.duql_finrank => Physics.FlavoredCyclicCoordinates.duql_finrank
assert_compatible GUT.FlavoredCyclicCoordinates.duql_forbidden => Physics.FlavoredCyclicCoordinates.duql_forbidden
assert_compatible GUT.FlavoredCyclicCoordinates.duueEquiv => Physics.FlavoredCyclicCoordinates.duueEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.duue_allowed => Physics.FlavoredCyclicCoordinates.duue_allowed
assert_compatible GUT.FlavoredCyclicCoordinates.duue_finrank => Physics.FlavoredCyclicCoordinates.duue_finrank
assert_compatible GUT.FlavoredCyclicCoordinates.duue_forbidden => Physics.FlavoredCyclicCoordinates.duue_forbidden
assert_compatible GUT.FlavoredCyclicCoordinates.fourBasis => Physics.FlavoredCyclicCoordinates.fourBasis
assert_compatible GUT.FlavoredCyclicCoordinates.fourBasis.eq_1 => Physics.FlavoredCyclicCoordinates.fourBasis.eq_1
assert_compatible GUT.FlavoredCyclicCoordinates.fourCharge => Physics.FlavoredCyclicCoordinates.fourCharge
assert_compatible GUT.FlavoredCyclicCoordinates.fourCharge.eq_1 => Physics.FlavoredCyclicCoordinates.fourCharge.eq_1
assert_compatible GUT.FlavoredCyclicCoordinates.four_weights => Physics.FlavoredCyclicCoordinates.four_weights
assert_compatible GUT.FlavoredCyclicCoordinates.llhhEquiv => Physics.FlavoredCyclicCoordinates.llhhEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.llhh_allowed => Physics.FlavoredCyclicCoordinates.llhh_allowed
assert_compatible GUT.FlavoredCyclicCoordinates.llhh_finrank => Physics.FlavoredCyclicCoordinates.llhh_finrank
assert_compatible GUT.FlavoredCyclicCoordinates.llhh_forbidden => Physics.FlavoredCyclicCoordinates.llhh_forbidden
assert_compatible GUT.FlavoredCyclicCoordinates.qqueBasis => Physics.FlavoredCyclicCoordinates.qqueBasis
assert_compatible GUT.FlavoredCyclicCoordinates.qqueBasis.eq_1 => Physics.FlavoredCyclicCoordinates.qqueBasis.eq_1
assert_compatible GUT.FlavoredCyclicCoordinates.qqueCharge => Physics.FlavoredCyclicCoordinates.qqueCharge
assert_compatible GUT.FlavoredCyclicCoordinates.qqueCharge.eq_1 => Physics.FlavoredCyclicCoordinates.qqueCharge.eq_1
assert_compatible GUT.FlavoredCyclicCoordinates.qqueEquiv => Physics.FlavoredCyclicCoordinates.qqueEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.qqueHomEquiv => Physics.FlavoredCyclicCoordinates.qqueHomEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.qqueSymmetricEquiv => Physics.FlavoredCyclicCoordinates.qqueSymmetricEquiv
assert_compatible GUT.FlavoredCyclicCoordinates.qque_allowed => Physics.FlavoredCyclicCoordinates.qque_allowed
assert_compatible GUT.FlavoredCyclicCoordinates.qque_finrank => Physics.FlavoredCyclicCoordinates.qque_finrank
assert_compatible GUT.FlavoredCyclicCoordinates.qque_forbidden => Physics.FlavoredCyclicCoordinates.qque_forbidden
assert_compatible GUT.FlavoredCyclicCoordinates.qque_weights => Physics.FlavoredCyclicCoordinates.qque_weights
