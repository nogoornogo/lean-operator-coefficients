import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkLocalBasis
import Physics.StandardModel.Operators.HeeckLeSixQuarkCertificate
import Physics.StandardModel.Operators.HeeckLeSixQuarkConvention
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkLocalBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkCertificate.coordinateEquiv.eq_1 => Physics.HeeckLeSixQuarkCertificate.coordinateEquiv.eq_1,
  GUT.HeeckLeSixQuarkLocalBasis.basis => Physics.HeeckLeSixQuarkLocalBasis.basis,
  GUT.HeeckLeSixQuarkLocalBasis.basis.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.basis.eq_1,
  GUT.HeeckLeSixQuarkLocalBasis.basis_apply => Physics.HeeckLeSixQuarkLocalBasis.basis_apply,
  GUT.HeeckLeSixQuarkLocalBasis.coordinate_assembly => Physics.HeeckLeSixQuarkLocalBasis.coordinate_assembly,
  GUT.HeeckLeSixQuarkLocalBasis.literal_reconstruction => Physics.HeeckLeSixQuarkLocalBasis.literal_reconstruction,
  GUT.HeeckLeSixQuarkLocalBasis.localEquiv => Physics.HeeckLeSixQuarkLocalBasis.localEquiv,
  GUT.HeeckLeSixQuarkLocalBasis.localEquiv.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.localEquiv.eq_1,
  GUT.HeeckLeSixQuarkLocalBasis.localEquiv_assembly => Physics.HeeckLeSixQuarkLocalBasis.localEquiv_assembly,
  GUT.HeeckLeSixQuarkLocalBasis.local_finrank => Physics.HeeckLeSixQuarkLocalBasis.local_finrank,
  GUT.HeeckLeSixQuarkLocalBasis.orbitInvariant => Physics.HeeckLeSixQuarkLocalBasis.orbitInvariant,
  GUT.HeeckLeSixQuarkLocalBasis.orbit_coordinates => Physics.HeeckLeSixQuarkLocalBasis.orbit_coordinates,
  GUT.HeeckLeSixQuarkLocalBasis.orbit_independent => Physics.HeeckLeSixQuarkLocalBasis.orbit_independent
]

assert_compatible GUT.HeeckLeSixQuarkCertificate.coordinateEquiv.eq_1 => Physics.HeeckLeSixQuarkCertificate.coordinateEquiv.eq_1
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.basis => Physics.HeeckLeSixQuarkLocalBasis.basis
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.basis.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.basis.eq_1
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.basis_apply => Physics.HeeckLeSixQuarkLocalBasis.basis_apply
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.coordinate_assembly => Physics.HeeckLeSixQuarkLocalBasis.coordinate_assembly
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.literal_reconstruction => Physics.HeeckLeSixQuarkLocalBasis.literal_reconstruction
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.localEquiv => Physics.HeeckLeSixQuarkLocalBasis.localEquiv
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.localEquiv.eq_1 => Physics.HeeckLeSixQuarkLocalBasis.localEquiv.eq_1
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.localEquiv_assembly => Physics.HeeckLeSixQuarkLocalBasis.localEquiv_assembly
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.local_finrank => Physics.HeeckLeSixQuarkLocalBasis.local_finrank
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.orbitInvariant => Physics.HeeckLeSixQuarkLocalBasis.orbitInvariant
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.orbit_coordinates => Physics.HeeckLeSixQuarkLocalBasis.orbit_coordinates
assert_compatible GUT.HeeckLeSixQuarkLocalBasis.orbit_independent => Physics.HeeckLeSixQuarkLocalBasis.orbit_independent
