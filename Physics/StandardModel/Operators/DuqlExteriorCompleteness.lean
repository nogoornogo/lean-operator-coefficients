import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlExteriorCompleteness
import Physics.StandardModel.Operators.DuqlOrderedCompleteness
import Math.RepresentationTheory.DistinctSpeciesAlternation
import Math.RepresentationTheory.FourTensorMultilinear
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlExteriorCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuqlExteriorCompleteness.Carrier => Physics.DuqlExteriorCompleteness.Carrier,
  GUT.DuqlExteriorCompleteness.Sector => Physics.DuqlExteriorCompleteness.Sector,
  GUT.DuqlExteriorCompleteness.exists_nonzero_iff => Physics.DuqlExteriorCompleteness.exists_nonzero_iff,
  GUT.DuqlExteriorCompleteness.homEquiv => Physics.DuqlExteriorCompleteness.homEquiv,
  GUT.DuqlExteriorCompleteness.instAddCommGroupCarrier => Physics.DuqlExteriorCompleteness.instAddCommGroupCarrier,
  GUT.DuqlExteriorCompleteness.instModuleComplexCarrier => Physics.DuqlExteriorCompleteness.instModuleComplexCarrier,
  GUT.DuqlExteriorCompleteness.orderedEquiv => Physics.DuqlExteriorCompleteness.orderedEquiv,
  GUT.DuqlExteriorCompleteness.species => Physics.DuqlExteriorCompleteness.species
]

assert_compatible GUT.DuqlExteriorCompleteness.Carrier => Physics.DuqlExteriorCompleteness.Carrier
assert_compatible GUT.DuqlExteriorCompleteness.Sector => Physics.DuqlExteriorCompleteness.Sector
assert_compatible GUT.DuqlExteriorCompleteness.exists_nonzero_iff => Physics.DuqlExteriorCompleteness.exists_nonzero_iff
assert_compatible GUT.DuqlExteriorCompleteness.homEquiv => Physics.DuqlExteriorCompleteness.homEquiv
assert_compatible GUT.DuqlExteriorCompleteness.instAddCommGroupCarrier => Physics.DuqlExteriorCompleteness.instAddCommGroupCarrier
assert_compatible GUT.DuqlExteriorCompleteness.instModuleComplexCarrier => Physics.DuqlExteriorCompleteness.instModuleComplexCarrier
assert_compatible GUT.DuqlExteriorCompleteness.orderedEquiv => Physics.DuqlExteriorCompleteness.orderedEquiv
assert_compatible GUT.DuqlExteriorCompleteness.species => Physics.DuqlExteriorCompleteness.species
