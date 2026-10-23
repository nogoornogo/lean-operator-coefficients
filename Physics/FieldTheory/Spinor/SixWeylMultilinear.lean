import Physics.FieldTheory.Spinor.Weyl.SixWeylMultilinear
import Physics.FieldTheory.Spinor.SixWeylInvariant
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.SixWeylMultilinear instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixWeylMultilinear.Coefficient => Physics.SixWeylMultilinear.Coefficient,
  GUT.SixWeylMultilinear.IsInvariant => Physics.SixWeylMultilinear.IsInvariant,
  GUT.SixWeylMultilinear.Spin => Physics.SixWeylMultilinear.Spin,
  GUT.SixWeylMultilinear.basisValue => Physics.SixWeylMultilinear.basisValue,
  GUT.SixWeylMultilinear.basisValue.eq_1 => Physics.SixWeylMultilinear.basisValue.eq_1,
  GUT.SixWeylMultilinear.basis_ext => Physics.SixWeylMultilinear.basis_ext,
  GUT.SixWeylMultilinear.coordinates => Physics.SixWeylMultilinear.coordinates,
  GUT.SixWeylMultilinear.coordinates.eq_1 => Physics.SixWeylMultilinear.coordinates.eq_1,
  GUT.SixWeylMultilinear.coordinates_reconstruct => Physics.SixWeylMultilinear.coordinates_reconstruct,
  GUT.SixWeylMultilinear.curried => Physics.SixWeylMultilinear.curried,
  GUT.SixWeylMultilinear.curried.eq_1 => Physics.SixWeylMultilinear.curried.eq_1,
  GUT.SixWeylMultilinear.curried_apply => Physics.SixWeylMultilinear.curried_apply,
  GUT.SixWeylMultilinear.eq_of_coordinates => Physics.SixWeylMultilinear.eq_of_coordinates,
  GUT.SixWeylMultilinear.existsUnique_pairing_coordinates => Physics.SixWeylMultilinear.existsUnique_pairing_coordinates,
  GUT.SixWeylMultilinear.exists_pairing_coordinates => Physics.SixWeylMultilinear.exists_pairing_coordinates,
  GUT.SixWeylMultilinear.pairing => Physics.SixWeylMultilinear.pairing,
  GUT.SixWeylMultilinear.pairingValue => Physics.SixWeylMultilinear.pairingValue,
  GUT.SixWeylMultilinear.pairingValue.eq_1 => Physics.SixWeylMultilinear.pairingValue.eq_1,
  GUT.SixWeylMultilinear.pairing_apply => Physics.SixWeylMultilinear.pairing_apply,
  GUT.SixWeylMultilinear.pairing_invariant => Physics.SixWeylMultilinear.pairing_invariant,
  GUT.SixWeylMultilinear.reconstruct => Physics.SixWeylMultilinear.reconstruct,
  GUT.SixWeylMultilinear.reconstruct.eq_1 => Physics.SixWeylMultilinear.reconstruct.eq_1,
  GUT.SixWeylMultilinear.reconstruct_coordinates => Physics.SixWeylMultilinear.reconstruct_coordinates
]

assert_compatible GUT.SixWeylMultilinear.Coefficient => Physics.SixWeylMultilinear.Coefficient
assert_compatible GUT.SixWeylMultilinear.IsInvariant => Physics.SixWeylMultilinear.IsInvariant
assert_compatible GUT.SixWeylMultilinear.Spin => Physics.SixWeylMultilinear.Spin
assert_compatible GUT.SixWeylMultilinear.basisValue => Physics.SixWeylMultilinear.basisValue
assert_compatible GUT.SixWeylMultilinear.basisValue.eq_1 => Physics.SixWeylMultilinear.basisValue.eq_1
assert_compatible GUT.SixWeylMultilinear.basis_ext => Physics.SixWeylMultilinear.basis_ext
assert_compatible GUT.SixWeylMultilinear.coordinates => Physics.SixWeylMultilinear.coordinates
assert_compatible GUT.SixWeylMultilinear.coordinates.eq_1 => Physics.SixWeylMultilinear.coordinates.eq_1
assert_compatible GUT.SixWeylMultilinear.coordinates_reconstruct => Physics.SixWeylMultilinear.coordinates_reconstruct
assert_compatible GUT.SixWeylMultilinear.curried => Physics.SixWeylMultilinear.curried
assert_compatible GUT.SixWeylMultilinear.curried.eq_1 => Physics.SixWeylMultilinear.curried.eq_1
assert_compatible GUT.SixWeylMultilinear.curried_apply => Physics.SixWeylMultilinear.curried_apply
assert_compatible GUT.SixWeylMultilinear.eq_of_coordinates => Physics.SixWeylMultilinear.eq_of_coordinates
assert_compatible GUT.SixWeylMultilinear.existsUnique_pairing_coordinates => Physics.SixWeylMultilinear.existsUnique_pairing_coordinates
assert_compatible GUT.SixWeylMultilinear.exists_pairing_coordinates => Physics.SixWeylMultilinear.exists_pairing_coordinates
assert_compatible GUT.SixWeylMultilinear.pairing => Physics.SixWeylMultilinear.pairing
assert_compatible GUT.SixWeylMultilinear.pairingValue => Physics.SixWeylMultilinear.pairingValue
assert_compatible GUT.SixWeylMultilinear.pairingValue.eq_1 => Physics.SixWeylMultilinear.pairingValue.eq_1
assert_compatible GUT.SixWeylMultilinear.pairing_apply => Physics.SixWeylMultilinear.pairing_apply
assert_compatible GUT.SixWeylMultilinear.pairing_invariant => Physics.SixWeylMultilinear.pairing_invariant
assert_compatible GUT.SixWeylMultilinear.reconstruct => Physics.SixWeylMultilinear.reconstruct
assert_compatible GUT.SixWeylMultilinear.reconstruct.eq_1 => Physics.SixWeylMultilinear.reconstruct.eq_1
assert_compatible GUT.SixWeylMultilinear.reconstruct_coordinates => Physics.SixWeylMultilinear.reconstruct_coordinates
