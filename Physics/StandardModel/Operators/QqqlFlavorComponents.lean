import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFlavorComponents
import Physics.StandardModel.Operators.QqqlExteriorCompleteness
import Math.RepresentationTheory.TripleMixedCoordinates
import Math.RepresentationTheory.TripleFlavorCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFlavorComponents instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlFlavorComponents.Condition => Physics.QqqlFlavorComponents.Condition,
  GUT.QqqlFlavorComponents.Family => Physics.QqqlFlavorComponents.Family,
  GUT.QqqlFlavorComponents.component_relations => Physics.QqqlFlavorComponents.component_relations,
  GUT.QqqlFlavorComponents.condition_iff => Physics.QqqlFlavorComponents.condition_iff,
  GUT.QqqlFlavorComponents.condition_iff_component_relations => Physics.QqqlFlavorComponents.condition_iff_component_relations,
  GUT.QqqlFlavorComponents.exteriorEquiv => Physics.QqqlFlavorComponents.exteriorEquiv,
  GUT.QqqlFlavorComponents.flavorCoordinates => Physics.QqqlFlavorComponents.flavorCoordinates,
  GUT.QqqlFlavorComponents.flavorCoordinates_injective => Physics.QqqlFlavorComponents.flavorCoordinates_injective,
  GUT.QqqlFlavorComponents.flavorTable => Physics.QqqlFlavorComponents.flavorTable,
  GUT.QqqlFlavorComponents.flavorTable_ext => Physics.QqqlFlavorComponents.flavorTable_ext,
  GUT.QqqlFlavorComponents.inverse_left => Physics.QqqlFlavorComponents.inverse_left,
  GUT.QqqlFlavorComponents.inverse_right => Physics.QqqlFlavorComponents.inverse_right,
  GUT.QqqlFlavorComponents.mem_residualSpace_iff => Physics.QqqlFlavorComponents.mem_residualSpace_iff,
  GUT.QqqlFlavorComponents.mixedCoordinates => Physics.QqqlFlavorComponents.mixedCoordinates,
  GUT.QqqlFlavorComponents.mixedTable => Physics.QqqlFlavorComponents.mixedTable,
  GUT.QqqlFlavorComponents.mixed_reconstruction => Physics.QqqlFlavorComponents.mixed_reconstruction,
  GUT.QqqlFlavorComponents.residualEquiv => Physics.QqqlFlavorComponents.residualEquiv,
  GUT.QqqlFlavorComponents.residualSpace => Physics.QqqlFlavorComponents.residualSpace,
  GUT.QqqlFlavorComponents.values => Physics.QqqlFlavorComponents.values,
  GUT.QqqlFlavorComponents.values.eq_1 => Physics.QqqlFlavorComponents.values.eq_1,
  GUT.QqqlFlavorComponents.values_assemble => Physics.QqqlFlavorComponents.values_assemble,
  GUT.QqqlFlavorComponents.values_extract => Physics.QqqlFlavorComponents.values_extract
]

assert_compatible GUT.QqqlFlavorComponents.Condition => Physics.QqqlFlavorComponents.Condition
assert_compatible GUT.QqqlFlavorComponents.Family => Physics.QqqlFlavorComponents.Family
assert_compatible GUT.QqqlFlavorComponents.component_relations => Physics.QqqlFlavorComponents.component_relations
assert_compatible GUT.QqqlFlavorComponents.condition_iff => Physics.QqqlFlavorComponents.condition_iff
assert_compatible GUT.QqqlFlavorComponents.condition_iff_component_relations => Physics.QqqlFlavorComponents.condition_iff_component_relations
assert_compatible GUT.QqqlFlavorComponents.exteriorEquiv => Physics.QqqlFlavorComponents.exteriorEquiv
assert_compatible GUT.QqqlFlavorComponents.flavorCoordinates => Physics.QqqlFlavorComponents.flavorCoordinates
assert_compatible GUT.QqqlFlavorComponents.flavorCoordinates_injective => Physics.QqqlFlavorComponents.flavorCoordinates_injective
assert_compatible GUT.QqqlFlavorComponents.flavorTable => Physics.QqqlFlavorComponents.flavorTable
assert_compatible GUT.QqqlFlavorComponents.flavorTable_ext => Physics.QqqlFlavorComponents.flavorTable_ext
assert_compatible GUT.QqqlFlavorComponents.inverse_left => Physics.QqqlFlavorComponents.inverse_left
assert_compatible GUT.QqqlFlavorComponents.inverse_right => Physics.QqqlFlavorComponents.inverse_right
assert_compatible GUT.QqqlFlavorComponents.mem_residualSpace_iff => Physics.QqqlFlavorComponents.mem_residualSpace_iff
assert_compatible GUT.QqqlFlavorComponents.mixedCoordinates => Physics.QqqlFlavorComponents.mixedCoordinates
assert_compatible GUT.QqqlFlavorComponents.mixedTable => Physics.QqqlFlavorComponents.mixedTable
assert_compatible GUT.QqqlFlavorComponents.mixed_reconstruction => Physics.QqqlFlavorComponents.mixed_reconstruction
assert_compatible GUT.QqqlFlavorComponents.residualEquiv => Physics.QqqlFlavorComponents.residualEquiv
assert_compatible GUT.QqqlFlavorComponents.residualSpace => Physics.QqqlFlavorComponents.residualSpace
assert_compatible GUT.QqqlFlavorComponents.values => Physics.QqqlFlavorComponents.values
assert_compatible GUT.QqqlFlavorComponents.values.eq_1 => Physics.QqqlFlavorComponents.values.eq_1
assert_compatible GUT.QqqlFlavorComponents.values_assemble => Physics.QqqlFlavorComponents.values_assemble
assert_compatible GUT.QqqlFlavorComponents.values_extract => Physics.QqqlFlavorComponents.values_extract
