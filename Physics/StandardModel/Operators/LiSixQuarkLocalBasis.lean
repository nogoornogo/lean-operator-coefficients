import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.LiSixQuarkCertificate
import Physics.StandardModel.Operators.LiSixQuarkConvention
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkCertificate.coordinateEquiv.eq_1 => Physics.LiSixQuarkCertificate.coordinateEquiv.eq_1,
  GUT.LiSixQuarkLocalBasis.basis => Physics.LiSixQuarkLocalBasis.basis,
  GUT.LiSixQuarkLocalBasis.basis.eq_1 => Physics.LiSixQuarkLocalBasis.basis.eq_1,
  GUT.LiSixQuarkLocalBasis.basis_apply => Physics.LiSixQuarkLocalBasis.basis_apply,
  GUT.LiSixQuarkLocalBasis.coordinate_assembly => Physics.LiSixQuarkLocalBasis.coordinate_assembly,
  GUT.LiSixQuarkLocalBasis.literal_reconstruction => Physics.LiSixQuarkLocalBasis.literal_reconstruction,
  GUT.LiSixQuarkLocalBasis.localEquiv => Physics.LiSixQuarkLocalBasis.localEquiv,
  GUT.LiSixQuarkLocalBasis.localEquiv.eq_1 => Physics.LiSixQuarkLocalBasis.localEquiv.eq_1,
  GUT.LiSixQuarkLocalBasis.localEquiv_assembly => Physics.LiSixQuarkLocalBasis.localEquiv_assembly,
  GUT.LiSixQuarkLocalBasis.local_finrank => Physics.LiSixQuarkLocalBasis.local_finrank,
  GUT.LiSixQuarkLocalBasis.orbitCoefficient => Physics.LiSixQuarkLocalBasis.orbitCoefficient,
  GUT.LiSixQuarkLocalBasis.orbitCoefficient.eq_1 => Physics.LiSixQuarkLocalBasis.orbitCoefficient.eq_1,
  GUT.LiSixQuarkLocalBasis.orbitCoefficient_eq => Physics.LiSixQuarkLocalBasis.orbitCoefficient_eq,
  GUT.LiSixQuarkLocalBasis.orbitInvariant => Physics.LiSixQuarkLocalBasis.orbitInvariant,
  GUT.LiSixQuarkLocalBasis.orbit_coordinates => Physics.LiSixQuarkLocalBasis.orbit_coordinates,
  GUT.LiSixQuarkLocalBasis.orbit_independent => Physics.LiSixQuarkLocalBasis.orbit_independent,
  GUT.LiSixQuarkLocalBasis.wordCoefficient => Physics.LiSixQuarkLocalBasis.wordCoefficient,
  GUT.LiSixQuarkLocalBasis.word_reconstruct => Physics.LiSixQuarkLocalBasis.word_reconstruct
]

assert_compatible GUT.LiSixQuarkCertificate.coordinateEquiv.eq_1 => Physics.LiSixQuarkCertificate.coordinateEquiv.eq_1
assert_compatible GUT.LiSixQuarkLocalBasis.basis => Physics.LiSixQuarkLocalBasis.basis
assert_compatible GUT.LiSixQuarkLocalBasis.basis.eq_1 => Physics.LiSixQuarkLocalBasis.basis.eq_1
assert_compatible GUT.LiSixQuarkLocalBasis.basis_apply => Physics.LiSixQuarkLocalBasis.basis_apply
assert_compatible GUT.LiSixQuarkLocalBasis.coordinate_assembly => Physics.LiSixQuarkLocalBasis.coordinate_assembly
assert_compatible GUT.LiSixQuarkLocalBasis.literal_reconstruction => Physics.LiSixQuarkLocalBasis.literal_reconstruction
assert_compatible GUT.LiSixQuarkLocalBasis.localEquiv => Physics.LiSixQuarkLocalBasis.localEquiv
assert_compatible GUT.LiSixQuarkLocalBasis.localEquiv.eq_1 => Physics.LiSixQuarkLocalBasis.localEquiv.eq_1
assert_compatible GUT.LiSixQuarkLocalBasis.localEquiv_assembly => Physics.LiSixQuarkLocalBasis.localEquiv_assembly
assert_compatible GUT.LiSixQuarkLocalBasis.local_finrank => Physics.LiSixQuarkLocalBasis.local_finrank
assert_compatible GUT.LiSixQuarkLocalBasis.orbitCoefficient => Physics.LiSixQuarkLocalBasis.orbitCoefficient
assert_compatible GUT.LiSixQuarkLocalBasis.orbitCoefficient.eq_1 => Physics.LiSixQuarkLocalBasis.orbitCoefficient.eq_1
assert_compatible GUT.LiSixQuarkLocalBasis.orbitCoefficient_eq => Physics.LiSixQuarkLocalBasis.orbitCoefficient_eq
assert_compatible GUT.LiSixQuarkLocalBasis.orbitInvariant => Physics.LiSixQuarkLocalBasis.orbitInvariant
assert_compatible GUT.LiSixQuarkLocalBasis.orbit_coordinates => Physics.LiSixQuarkLocalBasis.orbit_coordinates
assert_compatible GUT.LiSixQuarkLocalBasis.orbit_independent => Physics.LiSixQuarkLocalBasis.orbit_independent
assert_compatible GUT.LiSixQuarkLocalBasis.wordCoefficient => Physics.LiSixQuarkLocalBasis.wordCoefficient
assert_compatible GUT.LiSixQuarkLocalBasis.word_reconstruct => Physics.LiSixQuarkLocalBasis.word_reconstruct
