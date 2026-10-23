import Physics.FieldTheory.Spinor.Tensors.SixWeylInvariant
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Tensors.SixWeylInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixWeylInvariant.Coefficient => Physics.SixWeylInvariant.Coefficient,
  GUT.SixWeylInvariant.IsInvariant => Physics.SixWeylInvariant.IsInvariant,
  GUT.SixWeylInvariant.Spin => Physics.SixWeylInvariant.Spin,
  GUT.SixWeylInvariant.basisValue => Physics.SixWeylInvariant.basisValue,
  GUT.SixWeylInvariant.basisValue.eq_1 => Physics.SixWeylInvariant.basisValue.eq_1,
  GUT.SixWeylInvariant.basisValue_vanish => Physics.SixWeylInvariant.basisValue_vanish,
  GUT.SixWeylInvariant.basis_ext => Physics.SixWeylInvariant.basis_ext,
  GUT.SixWeylInvariant.exists_pairing_coordinates => Physics.SixWeylInvariant.exists_pairing_coordinates,
  GUT.SixWeylInvariant.pairingValue => Physics.SixWeylInvariant.pairingValue,
  GUT.SixWeylInvariant.pairingValue.eq_1 => Physics.SixWeylInvariant.pairingValue.eq_1,
  GUT.SixWeylInvariant.pairingValue.eq_2 => Physics.SixWeylInvariant.pairingValue.eq_2,
  GUT.SixWeylInvariant.pairingValue.eq_3 => Physics.SixWeylInvariant.pairingValue.eq_3,
  GUT.SixWeylInvariant.pairingValue.eq_4 => Physics.SixWeylInvariant.pairingValue.eq_4,
  GUT.SixWeylInvariant.pairingValue.eq_5 => Physics.SixWeylInvariant.pairingValue.eq_5
]

assert_compatible GUT.SixWeylInvariant.Coefficient => Physics.SixWeylInvariant.Coefficient
assert_compatible GUT.SixWeylInvariant.IsInvariant => Physics.SixWeylInvariant.IsInvariant
assert_compatible GUT.SixWeylInvariant.Spin => Physics.SixWeylInvariant.Spin
assert_compatible GUT.SixWeylInvariant.basisValue => Physics.SixWeylInvariant.basisValue
assert_compatible GUT.SixWeylInvariant.basisValue.eq_1 => Physics.SixWeylInvariant.basisValue.eq_1
assert_compatible GUT.SixWeylInvariant.basisValue_vanish => Physics.SixWeylInvariant.basisValue_vanish
assert_compatible GUT.SixWeylInvariant.basis_ext => Physics.SixWeylInvariant.basis_ext
assert_compatible GUT.SixWeylInvariant.exists_pairing_coordinates => Physics.SixWeylInvariant.exists_pairing_coordinates
assert_compatible GUT.SixWeylInvariant.pairingValue => Physics.SixWeylInvariant.pairingValue
assert_compatible GUT.SixWeylInvariant.pairingValue.eq_1 => Physics.SixWeylInvariant.pairingValue.eq_1
assert_compatible GUT.SixWeylInvariant.pairingValue.eq_2 => Physics.SixWeylInvariant.pairingValue.eq_2
assert_compatible GUT.SixWeylInvariant.pairingValue.eq_3 => Physics.SixWeylInvariant.pairingValue.eq_3
assert_compatible GUT.SixWeylInvariant.pairingValue.eq_4 => Physics.SixWeylInvariant.pairingValue.eq_4
assert_compatible GUT.SixWeylInvariant.pairingValue.eq_5 => Physics.SixWeylInvariant.pairingValue.eq_5
