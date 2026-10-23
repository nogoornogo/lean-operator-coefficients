import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTwoCoordinates
import Physics.StandardModel.Operators.SixQuarkSpeciesQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTwoCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkTwoCoordinates.Sector => Physics.SixQuarkTwoCoordinates.Sector,
  GUT.SixQuarkTwoCoordinates.finrank_sector => Physics.SixQuarkTwoCoordinates.finrank_sector,
  GUT.SixQuarkTwoCoordinates.inverse_probes => Physics.SixQuarkTwoCoordinates.inverse_probes,
  GUT.SixQuarkTwoCoordinates.liftCoefficient => Physics.SixQuarkTwoCoordinates.liftCoefficient,
  GUT.SixQuarkTwoCoordinates.liftCoefficient_restrictSector => Physics.SixQuarkTwoCoordinates.liftCoefficient_restrictSector,
  GUT.SixQuarkTwoCoordinates.orderedIntertwiner => Physics.SixQuarkTwoCoordinates.orderedIntertwiner,
  GUT.SixQuarkTwoCoordinates.orderedIntertwiner_toLinearMap => Physics.SixQuarkTwoCoordinates.orderedIntertwiner_toLinearMap,
  GUT.SixQuarkTwoCoordinates.orderedLift => Physics.SixQuarkTwoCoordinates.orderedLift,
  GUT.SixQuarkTwoCoordinates.orderedLift.eq_1 => Physics.SixQuarkTwoCoordinates.orderedLift.eq_1,
  GUT.SixQuarkTwoCoordinates.orderedLift_apply => Physics.SixQuarkTwoCoordinates.orderedLift_apply,
  GUT.SixQuarkTwoCoordinates.probes_inverse => Physics.SixQuarkTwoCoordinates.probes_inverse,
  GUT.SixQuarkTwoCoordinates.restrictSector => Physics.SixQuarkTwoCoordinates.restrictSector,
  GUT.SixQuarkTwoCoordinates.restrictSector.eq_1 => Physics.SixQuarkTwoCoordinates.restrictSector.eq_1,
  GUT.SixQuarkTwoCoordinates.restrictionEquiv => Physics.SixQuarkTwoCoordinates.restrictionEquiv,
  GUT.SixQuarkTwoCoordinates.restriction_liftCoefficient => Physics.SixQuarkTwoCoordinates.restriction_liftCoefficient,
  GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv,
  GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv_apply => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv_apply,
  GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv_symm_apply => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv_symm_apply
]

assert_compatible GUT.SixQuarkTwoCoordinates.Sector => Physics.SixQuarkTwoCoordinates.Sector
assert_compatible GUT.SixQuarkTwoCoordinates.finrank_sector => Physics.SixQuarkTwoCoordinates.finrank_sector
assert_compatible GUT.SixQuarkTwoCoordinates.inverse_probes => Physics.SixQuarkTwoCoordinates.inverse_probes
assert_compatible GUT.SixQuarkTwoCoordinates.liftCoefficient => Physics.SixQuarkTwoCoordinates.liftCoefficient
assert_compatible GUT.SixQuarkTwoCoordinates.liftCoefficient_restrictSector => Physics.SixQuarkTwoCoordinates.liftCoefficient_restrictSector
assert_compatible GUT.SixQuarkTwoCoordinates.orderedIntertwiner => Physics.SixQuarkTwoCoordinates.orderedIntertwiner
assert_compatible GUT.SixQuarkTwoCoordinates.orderedIntertwiner_toLinearMap => Physics.SixQuarkTwoCoordinates.orderedIntertwiner_toLinearMap
assert_compatible GUT.SixQuarkTwoCoordinates.orderedLift => Physics.SixQuarkTwoCoordinates.orderedLift
assert_compatible GUT.SixQuarkTwoCoordinates.orderedLift.eq_1 => Physics.SixQuarkTwoCoordinates.orderedLift.eq_1
assert_compatible GUT.SixQuarkTwoCoordinates.orderedLift_apply => Physics.SixQuarkTwoCoordinates.orderedLift_apply
assert_compatible GUT.SixQuarkTwoCoordinates.probes_inverse => Physics.SixQuarkTwoCoordinates.probes_inverse
assert_compatible GUT.SixQuarkTwoCoordinates.restrictSector => Physics.SixQuarkTwoCoordinates.restrictSector
assert_compatible GUT.SixQuarkTwoCoordinates.restrictSector.eq_1 => Physics.SixQuarkTwoCoordinates.restrictSector.eq_1
assert_compatible GUT.SixQuarkTwoCoordinates.restrictionEquiv => Physics.SixQuarkTwoCoordinates.restrictionEquiv
assert_compatible GUT.SixQuarkTwoCoordinates.restriction_liftCoefficient => Physics.SixQuarkTwoCoordinates.restriction_liftCoefficient
assert_compatible GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv
assert_compatible GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv_apply => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv_apply
assert_compatible GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv_symm_apply => Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv_symm_apply
