import Physics.FieldTheory.Mass.Surplus.SpeciesSectorPresentation
import Physics.FieldTheory.Mass.PhysicalSpeciesCopySurplus
import Physics.FieldTheory.Mass.BipartiteNormalForm
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.SpeciesSectorPresentation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SpeciesSectorPresentation.Presentation => Physics.SpeciesSectorPresentation.Presentation,
  GUT.SpeciesSectorPresentation.Presentation.casesOn => Physics.SpeciesSectorPresentation.Presentation.casesOn,
  GUT.SpeciesSectorPresentation.Presentation.coordinates => Physics.SpeciesSectorPresentation.Presentation.coordinates,
  GUT.SpeciesSectorPresentation.Presentation.copyMap => Physics.SpeciesSectorPresentation.Presentation.copyMap,
  GUT.SpeciesSectorPresentation.Presentation.ctorIdx => Physics.SpeciesSectorPresentation.Presentation.ctorIdx,
  GUT.SpeciesSectorPresentation.Presentation.dualField => Physics.SpeciesSectorPresentation.Presentation.dualField,
  GUT.SpeciesSectorPresentation.Presentation.factor => Physics.SpeciesSectorPresentation.Presentation.factor,
  GUT.SpeciesSectorPresentation.Presentation.massMap => Physics.SpeciesSectorPresentation.Presentation.massMap,
  GUT.SpeciesSectorPresentation.Presentation.mass_column => Physics.SpeciesSectorPresentation.Presentation.mass_column,
  GUT.SpeciesSectorPresentation.Presentation.mass_factor => Physics.SpeciesSectorPresentation.Presentation.mass_factor,
  GUT.SpeciesSectorPresentation.Presentation.mk => Physics.SpeciesSectorPresentation.Presentation.mk,
  GUT.SpeciesSectorPresentation.Presentation.mk.inj => Physics.SpeciesSectorPresentation.Presentation.mk.inj,
  GUT.SpeciesSectorPresentation.Presentation.mk.injEq => Physics.SpeciesSectorPresentation.Presentation.mk.injEq,
  GUT.SpeciesSectorPresentation.Presentation.mk.noConfusion => Physics.SpeciesSectorPresentation.Presentation.mk.noConfusion,
  GUT.SpeciesSectorPresentation.Presentation.mk.sizeOf_spec => Physics.SpeciesSectorPresentation.Presentation.mk.sizeOf_spec,
  GUT.SpeciesSectorPresentation.Presentation.noConfusion => Physics.SpeciesSectorPresentation.Presentation.noConfusion,
  GUT.SpeciesSectorPresentation.Presentation.noConfusionType => Physics.SpeciesSectorPresentation.Presentation.noConfusionType,
  GUT.SpeciesSectorPresentation.Presentation.noRest => Physics.SpeciesSectorPresentation.Presentation.noRest,
  GUT.SpeciesSectorPresentation.Presentation.noSelf => Physics.SpeciesSectorPresentation.Presentation.noSelf,
  GUT.SpeciesSectorPresentation.Presentation.opposite => Physics.SpeciesSectorPresentation.Presentation.opposite,
  GUT.SpeciesSectorPresentation.Presentation.oppositeProjection => Physics.SpeciesSectorPresentation.Presentation.oppositeProjection,
  GUT.SpeciesSectorPresentation.Presentation.rawMass => Physics.SpeciesSectorPresentation.Presentation.rawMass,
  GUT.SpeciesSectorPresentation.Presentation.rec => Physics.SpeciesSectorPresentation.Presentation.rec,
  GUT.SpeciesSectorPresentation.Presentation.recOn => Physics.SpeciesSectorPresentation.Presentation.recOn,
  GUT.SpeciesSectorPresentation.Presentation.rest => Physics.SpeciesSectorPresentation.Presentation.rest,
  GUT.SpeciesSectorPresentation.Presentation.source => Physics.SpeciesSectorPresentation.Presentation.source,
  GUT.SpeciesSectorPresentation.Presentation.species => Physics.SpeciesSectorPresentation.Presentation.species,
  GUT.SpeciesSectorPresentation.modelOfPresentations => Physics.SpeciesSectorPresentation.modelOfPresentations,
  GUT.SpeciesSectorPresentation.ofIrreducible => Physics.SpeciesSectorPresentation.ofIrreducible
]

assert_compatible GUT.SpeciesSectorPresentation.Presentation => Physics.SpeciesSectorPresentation.Presentation
assert_compatible GUT.SpeciesSectorPresentation.Presentation.casesOn => Physics.SpeciesSectorPresentation.Presentation.casesOn
assert_compatible GUT.SpeciesSectorPresentation.Presentation.coordinates => Physics.SpeciesSectorPresentation.Presentation.coordinates
assert_compatible GUT.SpeciesSectorPresentation.Presentation.copyMap => Physics.SpeciesSectorPresentation.Presentation.copyMap
assert_compatible GUT.SpeciesSectorPresentation.Presentation.ctorIdx => Physics.SpeciesSectorPresentation.Presentation.ctorIdx
assert_compatible GUT.SpeciesSectorPresentation.Presentation.dualField => Physics.SpeciesSectorPresentation.Presentation.dualField
assert_compatible GUT.SpeciesSectorPresentation.Presentation.factor => Physics.SpeciesSectorPresentation.Presentation.factor
assert_compatible GUT.SpeciesSectorPresentation.Presentation.massMap => Physics.SpeciesSectorPresentation.Presentation.massMap
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mass_column => Physics.SpeciesSectorPresentation.Presentation.mass_column
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mass_factor => Physics.SpeciesSectorPresentation.Presentation.mass_factor
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mk => Physics.SpeciesSectorPresentation.Presentation.mk
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mk.inj => Physics.SpeciesSectorPresentation.Presentation.mk.inj
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mk.injEq => Physics.SpeciesSectorPresentation.Presentation.mk.injEq
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mk.noConfusion => Physics.SpeciesSectorPresentation.Presentation.mk.noConfusion
assert_compatible GUT.SpeciesSectorPresentation.Presentation.mk.sizeOf_spec => Physics.SpeciesSectorPresentation.Presentation.mk.sizeOf_spec
assert_compatible GUT.SpeciesSectorPresentation.Presentation.noConfusion => Physics.SpeciesSectorPresentation.Presentation.noConfusion
assert_compatible GUT.SpeciesSectorPresentation.Presentation.noConfusionType => Physics.SpeciesSectorPresentation.Presentation.noConfusionType
assert_compatible GUT.SpeciesSectorPresentation.Presentation.noRest => Physics.SpeciesSectorPresentation.Presentation.noRest
assert_compatible GUT.SpeciesSectorPresentation.Presentation.noSelf => Physics.SpeciesSectorPresentation.Presentation.noSelf
assert_compatible GUT.SpeciesSectorPresentation.Presentation.opposite => Physics.SpeciesSectorPresentation.Presentation.opposite
assert_compatible GUT.SpeciesSectorPresentation.Presentation.oppositeProjection => Physics.SpeciesSectorPresentation.Presentation.oppositeProjection
assert_compatible GUT.SpeciesSectorPresentation.Presentation.rawMass => Physics.SpeciesSectorPresentation.Presentation.rawMass
assert_compatible GUT.SpeciesSectorPresentation.Presentation.rec => Physics.SpeciesSectorPresentation.Presentation.rec
assert_compatible GUT.SpeciesSectorPresentation.Presentation.recOn => Physics.SpeciesSectorPresentation.Presentation.recOn
assert_compatible GUT.SpeciesSectorPresentation.Presentation.rest => Physics.SpeciesSectorPresentation.Presentation.rest
assert_compatible GUT.SpeciesSectorPresentation.Presentation.source => Physics.SpeciesSectorPresentation.Presentation.source
assert_compatible GUT.SpeciesSectorPresentation.Presentation.species => Physics.SpeciesSectorPresentation.Presentation.species
assert_compatible GUT.SpeciesSectorPresentation.modelOfPresentations => Physics.SpeciesSectorPresentation.modelOfPresentations
assert_compatible GUT.SpeciesSectorPresentation.ofIrreducible => Physics.SpeciesSectorPresentation.ofIrreducible
