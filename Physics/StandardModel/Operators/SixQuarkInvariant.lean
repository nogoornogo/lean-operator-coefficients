import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkInvariant
import Physics.StandardModel.Gauge.SixColorInvariant
import Physics.FieldTheory.Spinor.SixWeylMultilinear
import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Math.RepresentationTheory.SixSlotRestrictionLift
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkInvariant.Coefficient => Physics.SixQuarkInvariant.Coefficient,
  GUT.SixQuarkInvariant.IsInvariant => Physics.SixQuarkInvariant.IsInvariant,
  GUT.SixQuarkInvariant.IsSpeciesAlternating => Physics.SixQuarkInvariant.IsSpeciesAlternating,
  GUT.SixQuarkInvariant.Quark => Physics.SixQuarkInvariant.Quark,
  GUT.SixQuarkInvariant.Spin => Physics.SixQuarkInvariant.Spin,
  GUT.SixQuarkInvariant.colorAction => Physics.SixQuarkInvariant.colorAction,
  GUT.SixQuarkInvariant.colorAction.eq_1 => Physics.SixQuarkInvariant.colorAction.eq_1,
  GUT.SixQuarkInvariant.colorComponent => Physics.SixQuarkInvariant.colorComponent,
  GUT.SixQuarkInvariant.colorComponent.eq_1 => Physics.SixQuarkInvariant.colorComponent.eq_1,
  GUT.SixQuarkInvariant.colorComponent_tmul => Physics.SixQuarkInvariant.colorComponent_tmul,
  GUT.SixQuarkInvariant.colorProbe => Physics.SixQuarkInvariant.colorProbe,
  GUT.SixQuarkInvariant.colorProbe.eq_1 => Physics.SixQuarkInvariant.colorProbe.eq_1,
  GUT.SixQuarkInvariant.combine => Physics.SixQuarkInvariant.combine,
  GUT.SixQuarkInvariant.combine.eq_1 => Physics.SixQuarkInvariant.combine.eq_1,
  GUT.SixQuarkInvariant.combine_apply => Physics.SixQuarkInvariant.combine_apply,
  GUT.SixQuarkInvariant.coordinates => Physics.SixQuarkInvariant.coordinates,
  GUT.SixQuarkInvariant.coordinates.eq_1 => Physics.SixQuarkInvariant.coordinates.eq_1,
  GUT.SixQuarkInvariant.coordinates_formula => Physics.SixQuarkInvariant.coordinates_formula,
  GUT.SixQuarkInvariant.coordinates_reconstruct => Physics.SixQuarkInvariant.coordinates_reconstruct,
  GUT.SixQuarkInvariant.eq_of_coordinates => Physics.SixQuarkInvariant.eq_of_coordinates,
  GUT.SixQuarkInvariant.exists_product_coordinates => Physics.SixQuarkInvariant.exists_product_coordinates,
  GUT.SixQuarkInvariant.exteriorRestriction => Physics.SixQuarkInvariant.exteriorRestriction,
  GUT.SixQuarkInvariant.exteriorRestriction_apply => Physics.SixQuarkInvariant.exteriorRestriction_apply,
  GUT.SixQuarkInvariant.exteriorRestriction_product_coordinates => Physics.SixQuarkInvariant.exteriorRestriction_product_coordinates,
  GUT.SixQuarkInvariant.exteriorRestriction_speciesAlternating => Physics.SixQuarkInvariant.exteriorRestriction_speciesAlternating,
  GUT.SixQuarkInvariant.exterior_eq_of_coordinates => Physics.SixQuarkInvariant.exterior_eq_of_coordinates,
  GUT.SixQuarkInvariant.fixedColor => Physics.SixQuarkInvariant.fixedColor,
  GUT.SixQuarkInvariant.fixedColor_apply => Physics.SixQuarkInvariant.fixedColor_apply,
  GUT.SixQuarkInvariant.fixedColor_invariant => Physics.SixQuarkInvariant.fixedColor_invariant,
  GUT.SixQuarkInvariant.fixedSpin => Physics.SixQuarkInvariant.fixedSpin,
  GUT.SixQuarkInvariant.fixedSpin_apply => Physics.SixQuarkInvariant.fixedSpin_apply,
  GUT.SixQuarkInvariant.fixedSpin_invariant => Physics.SixQuarkInvariant.fixedSpin_invariant,
  GUT.SixQuarkInvariant.orderedCoefficient => Physics.SixQuarkInvariant.orderedCoefficient,
  GUT.SixQuarkInvariant.orderedCoefficient_apply => Physics.SixQuarkInvariant.orderedCoefficient_apply,
  GUT.SixQuarkInvariant.orderedCoefficient_invariant => Physics.SixQuarkInvariant.orderedCoefficient_invariant,
  GUT.SixQuarkInvariant.productPairing => Physics.SixQuarkInvariant.productPairing,
  GUT.SixQuarkInvariant.productPairing_apply => Physics.SixQuarkInvariant.productPairing_apply,
  GUT.SixQuarkInvariant.productPairing_invariant => Physics.SixQuarkInvariant.productPairing_invariant,
  GUT.SixQuarkInvariant.product_coordinates_unique => Physics.SixQuarkInvariant.product_coordinates_unique,
  GUT.SixQuarkInvariant.pure_ext => Physics.SixQuarkInvariant.pure_ext,
  GUT.SixQuarkInvariant.reconstruct => Physics.SixQuarkInvariant.reconstruct,
  GUT.SixQuarkInvariant.reconstruct.eq_1 => Physics.SixQuarkInvariant.reconstruct.eq_1,
  GUT.SixQuarkInvariant.reconstruct_apply => Physics.SixQuarkInvariant.reconstruct_apply,
  GUT.SixQuarkInvariant.reconstruct_coordinates => Physics.SixQuarkInvariant.reconstruct_coordinates,
  GUT.SixQuarkInvariant.reconstruct_invariant => Physics.SixQuarkInvariant.reconstruct_invariant,
  GUT.SixQuarkInvariant.species_coordinate_constraint => Physics.SixQuarkInvariant.species_coordinate_constraint,
  GUT.SixQuarkInvariant.spinAction => Physics.SixQuarkInvariant.spinAction,
  GUT.SixQuarkInvariant.spinAction.eq_1 => Physics.SixQuarkInvariant.spinAction.eq_1,
  GUT.SixQuarkInvariant.spinCoordinates => Physics.SixQuarkInvariant.spinCoordinates,
  GUT.SixQuarkInvariant.spinCoordinates.eq_1 => Physics.SixQuarkInvariant.spinCoordinates.eq_1,
  GUT.SixQuarkInvariant.spinCoordinates_apply => Physics.SixQuarkInvariant.spinCoordinates_apply,
  GUT.SixQuarkInvariant.spinCoordinates_invariant => Physics.SixQuarkInvariant.spinCoordinates_invariant
]

assert_compatible GUT.SixQuarkInvariant.Coefficient => Physics.SixQuarkInvariant.Coefficient
assert_compatible GUT.SixQuarkInvariant.IsInvariant => Physics.SixQuarkInvariant.IsInvariant
assert_compatible GUT.SixQuarkInvariant.IsSpeciesAlternating => Physics.SixQuarkInvariant.IsSpeciesAlternating
assert_compatible GUT.SixQuarkInvariant.Quark => Physics.SixQuarkInvariant.Quark
assert_compatible GUT.SixQuarkInvariant.Spin => Physics.SixQuarkInvariant.Spin
assert_compatible GUT.SixQuarkInvariant.colorAction => Physics.SixQuarkInvariant.colorAction
assert_compatible GUT.SixQuarkInvariant.colorAction.eq_1 => Physics.SixQuarkInvariant.colorAction.eq_1
assert_compatible GUT.SixQuarkInvariant.colorComponent => Physics.SixQuarkInvariant.colorComponent
assert_compatible GUT.SixQuarkInvariant.colorComponent.eq_1 => Physics.SixQuarkInvariant.colorComponent.eq_1
assert_compatible GUT.SixQuarkInvariant.colorComponent_tmul => Physics.SixQuarkInvariant.colorComponent_tmul
assert_compatible GUT.SixQuarkInvariant.colorProbe => Physics.SixQuarkInvariant.colorProbe
assert_compatible GUT.SixQuarkInvariant.colorProbe.eq_1 => Physics.SixQuarkInvariant.colorProbe.eq_1
assert_compatible GUT.SixQuarkInvariant.combine => Physics.SixQuarkInvariant.combine
assert_compatible GUT.SixQuarkInvariant.combine.eq_1 => Physics.SixQuarkInvariant.combine.eq_1
assert_compatible GUT.SixQuarkInvariant.combine_apply => Physics.SixQuarkInvariant.combine_apply
assert_compatible GUT.SixQuarkInvariant.coordinates => Physics.SixQuarkInvariant.coordinates
assert_compatible GUT.SixQuarkInvariant.coordinates.eq_1 => Physics.SixQuarkInvariant.coordinates.eq_1
assert_compatible GUT.SixQuarkInvariant.coordinates_formula => Physics.SixQuarkInvariant.coordinates_formula
assert_compatible GUT.SixQuarkInvariant.coordinates_reconstruct => Physics.SixQuarkInvariant.coordinates_reconstruct
assert_compatible GUT.SixQuarkInvariant.eq_of_coordinates => Physics.SixQuarkInvariant.eq_of_coordinates
assert_compatible GUT.SixQuarkInvariant.exists_product_coordinates => Physics.SixQuarkInvariant.exists_product_coordinates
assert_compatible GUT.SixQuarkInvariant.exteriorRestriction => Physics.SixQuarkInvariant.exteriorRestriction
assert_compatible GUT.SixQuarkInvariant.exteriorRestriction_apply => Physics.SixQuarkInvariant.exteriorRestriction_apply
assert_compatible GUT.SixQuarkInvariant.exteriorRestriction_product_coordinates => Physics.SixQuarkInvariant.exteriorRestriction_product_coordinates
assert_compatible GUT.SixQuarkInvariant.exteriorRestriction_speciesAlternating => Physics.SixQuarkInvariant.exteriorRestriction_speciesAlternating
assert_compatible GUT.SixQuarkInvariant.exterior_eq_of_coordinates => Physics.SixQuarkInvariant.exterior_eq_of_coordinates
assert_compatible GUT.SixQuarkInvariant.fixedColor => Physics.SixQuarkInvariant.fixedColor
assert_compatible GUT.SixQuarkInvariant.fixedColor_apply => Physics.SixQuarkInvariant.fixedColor_apply
assert_compatible GUT.SixQuarkInvariant.fixedColor_invariant => Physics.SixQuarkInvariant.fixedColor_invariant
assert_compatible GUT.SixQuarkInvariant.fixedSpin => Physics.SixQuarkInvariant.fixedSpin
assert_compatible GUT.SixQuarkInvariant.fixedSpin_apply => Physics.SixQuarkInvariant.fixedSpin_apply
assert_compatible GUT.SixQuarkInvariant.fixedSpin_invariant => Physics.SixQuarkInvariant.fixedSpin_invariant
assert_compatible GUT.SixQuarkInvariant.orderedCoefficient => Physics.SixQuarkInvariant.orderedCoefficient
assert_compatible GUT.SixQuarkInvariant.orderedCoefficient_apply => Physics.SixQuarkInvariant.orderedCoefficient_apply
assert_compatible GUT.SixQuarkInvariant.orderedCoefficient_invariant => Physics.SixQuarkInvariant.orderedCoefficient_invariant
assert_compatible GUT.SixQuarkInvariant.productPairing => Physics.SixQuarkInvariant.productPairing
assert_compatible GUT.SixQuarkInvariant.productPairing_apply => Physics.SixQuarkInvariant.productPairing_apply
assert_compatible GUT.SixQuarkInvariant.productPairing_invariant => Physics.SixQuarkInvariant.productPairing_invariant
assert_compatible GUT.SixQuarkInvariant.product_coordinates_unique => Physics.SixQuarkInvariant.product_coordinates_unique
assert_compatible GUT.SixQuarkInvariant.pure_ext => Physics.SixQuarkInvariant.pure_ext
assert_compatible GUT.SixQuarkInvariant.reconstruct => Physics.SixQuarkInvariant.reconstruct
assert_compatible GUT.SixQuarkInvariant.reconstruct.eq_1 => Physics.SixQuarkInvariant.reconstruct.eq_1
assert_compatible GUT.SixQuarkInvariant.reconstruct_apply => Physics.SixQuarkInvariant.reconstruct_apply
assert_compatible GUT.SixQuarkInvariant.reconstruct_coordinates => Physics.SixQuarkInvariant.reconstruct_coordinates
assert_compatible GUT.SixQuarkInvariant.reconstruct_invariant => Physics.SixQuarkInvariant.reconstruct_invariant
assert_compatible GUT.SixQuarkInvariant.species_coordinate_constraint => Physics.SixQuarkInvariant.species_coordinate_constraint
assert_compatible GUT.SixQuarkInvariant.spinAction => Physics.SixQuarkInvariant.spinAction
assert_compatible GUT.SixQuarkInvariant.spinAction.eq_1 => Physics.SixQuarkInvariant.spinAction.eq_1
assert_compatible GUT.SixQuarkInvariant.spinCoordinates => Physics.SixQuarkInvariant.spinCoordinates
assert_compatible GUT.SixQuarkInvariant.spinCoordinates.eq_1 => Physics.SixQuarkInvariant.spinCoordinates.eq_1
assert_compatible GUT.SixQuarkInvariant.spinCoordinates_apply => Physics.SixQuarkInvariant.spinCoordinates_apply
assert_compatible GUT.SixQuarkInvariant.spinCoordinates_invariant => Physics.SixQuarkInvariant.spinCoordinates_invariant
