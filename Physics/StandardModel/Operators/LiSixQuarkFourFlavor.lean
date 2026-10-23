import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFourFlavor
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFourFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkFourFlavor.D => Physics.LiSixQuarkFourFlavor.D,
  GUT.LiSixQuarkFourFlavor.U => Physics.LiSixQuarkFourFlavor.U,
  GUT.LiSixQuarkFourFlavor.V => Physics.LiSixQuarkFourFlavor.V,
  GUT.LiSixQuarkFourFlavor.admissibleHom => Physics.LiSixQuarkFourFlavor.admissibleHom,
  GUT.LiSixQuarkFourFlavor.determinantPerm => Physics.LiSixQuarkFourFlavor.determinantPerm,
  GUT.LiSixQuarkFourFlavor.determinantPerm.eq_1 => Physics.LiSixQuarkFourFlavor.determinantPerm.eq_1,
  GUT.LiSixQuarkFourFlavor.determinantSign => Physics.LiSixQuarkFourFlavor.determinantSign,
  GUT.LiSixQuarkFourFlavor.determinantSign.eq_1 => Physics.LiSixQuarkFourFlavor.determinantSign.eq_1,
  GUT.LiSixQuarkFourFlavor.down => Physics.LiSixQuarkFourFlavor.down,
  GUT.LiSixQuarkFourFlavor.flavor => Physics.LiSixQuarkFourFlavor.flavor,
  GUT.LiSixQuarkFourFlavor.flavorValue => Physics.LiSixQuarkFourFlavor.flavorValue,
  GUT.LiSixQuarkFourFlavor.flavorValue.eq_1 => Physics.LiSixQuarkFourFlavor.flavorValue.eq_1,
  GUT.LiSixQuarkFourFlavor.flavor_exchange => Physics.LiSixQuarkFourFlavor.flavor_exchange,
  GUT.LiSixQuarkFourFlavor.flavor_witness => Physics.LiSixQuarkFourFlavor.flavor_witness,
  GUT.LiSixQuarkFourFlavor.hom => Physics.LiSixQuarkFourFlavor.hom,
  GUT.LiSixQuarkFourFlavor.hom_coordinates => Physics.LiSixQuarkFourFlavor.hom_coordinates,
  GUT.LiSixQuarkFourFlavor.hom_nonzero => Physics.LiSixQuarkFourFlavor.hom_nonzero,
  GUT.LiSixQuarkFourFlavor.physical => Physics.LiSixQuarkFourFlavor.physical,
  GUT.LiSixQuarkFourFlavor.physical_nonzero => Physics.LiSixQuarkFourFlavor.physical_nonzero,
  GUT.LiSixQuarkFourFlavor.separating_probe_witness => Physics.LiSixQuarkFourFlavor.separating_probe_witness,
  GUT.LiSixQuarkFourFlavor.up => Physics.LiSixQuarkFourFlavor.up,
  GUT.LiSixQuarkFourFlavor.witness => Physics.LiSixQuarkFourFlavor.witness
]

assert_compatible GUT.LiSixQuarkFourFlavor.D => Physics.LiSixQuarkFourFlavor.D
assert_compatible GUT.LiSixQuarkFourFlavor.U => Physics.LiSixQuarkFourFlavor.U
assert_compatible GUT.LiSixQuarkFourFlavor.V => Physics.LiSixQuarkFourFlavor.V
assert_compatible GUT.LiSixQuarkFourFlavor.admissibleHom => Physics.LiSixQuarkFourFlavor.admissibleHom
assert_compatible GUT.LiSixQuarkFourFlavor.determinantPerm => Physics.LiSixQuarkFourFlavor.determinantPerm
assert_compatible GUT.LiSixQuarkFourFlavor.determinantPerm.eq_1 => Physics.LiSixQuarkFourFlavor.determinantPerm.eq_1
assert_compatible GUT.LiSixQuarkFourFlavor.determinantSign => Physics.LiSixQuarkFourFlavor.determinantSign
assert_compatible GUT.LiSixQuarkFourFlavor.determinantSign.eq_1 => Physics.LiSixQuarkFourFlavor.determinantSign.eq_1
assert_compatible GUT.LiSixQuarkFourFlavor.down => Physics.LiSixQuarkFourFlavor.down
assert_compatible GUT.LiSixQuarkFourFlavor.flavor => Physics.LiSixQuarkFourFlavor.flavor
assert_compatible GUT.LiSixQuarkFourFlavor.flavorValue => Physics.LiSixQuarkFourFlavor.flavorValue
assert_compatible GUT.LiSixQuarkFourFlavor.flavorValue.eq_1 => Physics.LiSixQuarkFourFlavor.flavorValue.eq_1
assert_compatible GUT.LiSixQuarkFourFlavor.flavor_exchange => Physics.LiSixQuarkFourFlavor.flavor_exchange
assert_compatible GUT.LiSixQuarkFourFlavor.flavor_witness => Physics.LiSixQuarkFourFlavor.flavor_witness
assert_compatible GUT.LiSixQuarkFourFlavor.hom => Physics.LiSixQuarkFourFlavor.hom
assert_compatible GUT.LiSixQuarkFourFlavor.hom_coordinates => Physics.LiSixQuarkFourFlavor.hom_coordinates
assert_compatible GUT.LiSixQuarkFourFlavor.hom_nonzero => Physics.LiSixQuarkFourFlavor.hom_nonzero
assert_compatible GUT.LiSixQuarkFourFlavor.physical => Physics.LiSixQuarkFourFlavor.physical
assert_compatible GUT.LiSixQuarkFourFlavor.physical_nonzero => Physics.LiSixQuarkFourFlavor.physical_nonzero
assert_compatible GUT.LiSixQuarkFourFlavor.separating_probe_witness => Physics.LiSixQuarkFourFlavor.separating_probe_witness
assert_compatible GUT.LiSixQuarkFourFlavor.up => Physics.LiSixQuarkFourFlavor.up
assert_compatible GUT.LiSixQuarkFourFlavor.witness => Physics.LiSixQuarkFourFlavor.witness
