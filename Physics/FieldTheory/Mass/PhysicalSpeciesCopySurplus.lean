import Physics.FieldTheory.Mass.Surplus.PhysicalSpeciesCopySurplus
import Physics.FieldTheory.Mass.PhysicalCommonCopyModel
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.PhysicalSpeciesCopySurplus instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PhysicalSpeciesCopySurplus.Model => Physics.PhysicalSpeciesCopySurplus.Model,
  GUT.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior => Physics.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior,
  GUT.PhysicalSpeciesCopySurplus.Model.casesOn => Physics.PhysicalSpeciesCopySurplus.Model.casesOn,
  GUT.PhysicalSpeciesCopySurplus.Model.ctorIdx => Physics.PhysicalSpeciesCopySurplus.Model.ctorIdx,
  GUT.PhysicalSpeciesCopySurplus.Model.mk => Physics.PhysicalSpeciesCopySurplus.Model.mk,
  GUT.PhysicalSpeciesCopySurplus.Model.mk.inj => Physics.PhysicalSpeciesCopySurplus.Model.mk.inj,
  GUT.PhysicalSpeciesCopySurplus.Model.mk.injEq => Physics.PhysicalSpeciesCopySurplus.Model.mk.injEq,
  GUT.PhysicalSpeciesCopySurplus.Model.mk.noConfusion => Physics.PhysicalSpeciesCopySurplus.Model.mk.noConfusion,
  GUT.PhysicalSpeciesCopySurplus.Model.mk.sizeOf_spec => Physics.PhysicalSpeciesCopySurplus.Model.mk.sizeOf_spec,
  GUT.PhysicalSpeciesCopySurplus.Model.noConfusion => Physics.PhysicalSpeciesCopySurplus.Model.noConfusion,
  GUT.PhysicalSpeciesCopySurplus.Model.noConfusionType => Physics.PhysicalSpeciesCopySurplus.Model.noConfusionType,
  GUT.PhysicalSpeciesCopySurplus.Model.realize => Physics.PhysicalSpeciesCopySurplus.Model.realize,
  GUT.PhysicalSpeciesCopySurplus.Model.rec => Physics.PhysicalSpeciesCopySurplus.Model.rec,
  GUT.PhysicalSpeciesCopySurplus.Model.recOn => Physics.PhysicalSpeciesCopySurplus.Model.recOn,
  GUT.PhysicalSpeciesCopySurplus.Realization => Physics.PhysicalSpeciesCopySurplus.Realization,
  GUT.PhysicalSpeciesCopySurplus.Realization.HasLightExterior => Physics.PhysicalSpeciesCopySurplus.Realization.HasLightExterior,
  GUT.PhysicalSpeciesCopySurplus.Realization.casesOn => Physics.PhysicalSpeciesCopySurplus.Realization.casesOn,
  GUT.PhysicalSpeciesCopySurplus.Realization.ctorIdx => Physics.PhysicalSpeciesCopySurplus.Realization.ctorIdx,
  GUT.PhysicalSpeciesCopySurplus.Realization.e => Physics.PhysicalSpeciesCopySurplus.Realization.e,
  GUT.PhysicalSpeciesCopySurplus.Realization.electronEq => Physics.PhysicalSpeciesCopySurplus.Realization.electronEq,
  GUT.PhysicalSpeciesCopySurplus.Realization.light_exterior => Physics.PhysicalSpeciesCopySurplus.Realization.light_exterior,
  GUT.PhysicalSpeciesCopySurplus.Realization.mk => Physics.PhysicalSpeciesCopySurplus.Realization.mk,
  GUT.PhysicalSpeciesCopySurplus.Realization.mk.inj => Physics.PhysicalSpeciesCopySurplus.Realization.mk.inj,
  GUT.PhysicalSpeciesCopySurplus.Realization.mk.injEq => Physics.PhysicalSpeciesCopySurplus.Realization.mk.injEq,
  GUT.PhysicalSpeciesCopySurplus.Realization.mk.noConfusion => Physics.PhysicalSpeciesCopySurplus.Realization.mk.noConfusion,
  GUT.PhysicalSpeciesCopySurplus.Realization.mk.sizeOf_spec => Physics.PhysicalSpeciesCopySurplus.Realization.mk.sizeOf_spec,
  GUT.PhysicalSpeciesCopySurplus.Realization.noConfusion => Physics.PhysicalSpeciesCopySurplus.Realization.noConfusion,
  GUT.PhysicalSpeciesCopySurplus.Realization.noConfusionType => Physics.PhysicalSpeciesCopySurplus.Realization.noConfusionType,
  GUT.PhysicalSpeciesCopySurplus.Realization.q => Physics.PhysicalSpeciesCopySurplus.Realization.q,
  GUT.PhysicalSpeciesCopySurplus.Realization.quarkEq => Physics.PhysicalSpeciesCopySurplus.Realization.quarkEq,
  GUT.PhysicalSpeciesCopySurplus.Realization.rec => Physics.PhysicalSpeciesCopySurplus.Realization.rec,
  GUT.PhysicalSpeciesCopySurplus.Realization.recOn => Physics.PhysicalSpeciesCopySurplus.Realization.recOn,
  GUT.PhysicalSpeciesCopySurplus.Realization.u => Physics.PhysicalSpeciesCopySurplus.Realization.u,
  GUT.PhysicalSpeciesCopySurplus.Realization.upEq => Physics.PhysicalSpeciesCopySurplus.Realization.upEq
]

assert_compatible GUT.PhysicalSpeciesCopySurplus.Model => Physics.PhysicalSpeciesCopySurplus.Model
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior => Physics.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.casesOn => Physics.PhysicalSpeciesCopySurplus.Model.casesOn
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.ctorIdx => Physics.PhysicalSpeciesCopySurplus.Model.ctorIdx
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.mk => Physics.PhysicalSpeciesCopySurplus.Model.mk
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.mk.inj => Physics.PhysicalSpeciesCopySurplus.Model.mk.inj
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.mk.injEq => Physics.PhysicalSpeciesCopySurplus.Model.mk.injEq
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.mk.noConfusion => Physics.PhysicalSpeciesCopySurplus.Model.mk.noConfusion
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.mk.sizeOf_spec => Physics.PhysicalSpeciesCopySurplus.Model.mk.sizeOf_spec
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.noConfusion => Physics.PhysicalSpeciesCopySurplus.Model.noConfusion
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.noConfusionType => Physics.PhysicalSpeciesCopySurplus.Model.noConfusionType
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.realize => Physics.PhysicalSpeciesCopySurplus.Model.realize
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.rec => Physics.PhysicalSpeciesCopySurplus.Model.rec
assert_compatible GUT.PhysicalSpeciesCopySurplus.Model.recOn => Physics.PhysicalSpeciesCopySurplus.Model.recOn
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization => Physics.PhysicalSpeciesCopySurplus.Realization
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.HasLightExterior => Physics.PhysicalSpeciesCopySurplus.Realization.HasLightExterior
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.casesOn => Physics.PhysicalSpeciesCopySurplus.Realization.casesOn
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.ctorIdx => Physics.PhysicalSpeciesCopySurplus.Realization.ctorIdx
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.e => Physics.PhysicalSpeciesCopySurplus.Realization.e
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.electronEq => Physics.PhysicalSpeciesCopySurplus.Realization.electronEq
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.light_exterior => Physics.PhysicalSpeciesCopySurplus.Realization.light_exterior
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.mk => Physics.PhysicalSpeciesCopySurplus.Realization.mk
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.mk.inj => Physics.PhysicalSpeciesCopySurplus.Realization.mk.inj
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.mk.injEq => Physics.PhysicalSpeciesCopySurplus.Realization.mk.injEq
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.mk.noConfusion => Physics.PhysicalSpeciesCopySurplus.Realization.mk.noConfusion
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.mk.sizeOf_spec => Physics.PhysicalSpeciesCopySurplus.Realization.mk.sizeOf_spec
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.noConfusion => Physics.PhysicalSpeciesCopySurplus.Realization.noConfusion
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.noConfusionType => Physics.PhysicalSpeciesCopySurplus.Realization.noConfusionType
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.q => Physics.PhysicalSpeciesCopySurplus.Realization.q
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.quarkEq => Physics.PhysicalSpeciesCopySurplus.Realization.quarkEq
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.rec => Physics.PhysicalSpeciesCopySurplus.Realization.rec
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.recOn => Physics.PhysicalSpeciesCopySurplus.Realization.recOn
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.u => Physics.PhysicalSpeciesCopySurplus.Realization.u
assert_compatible GUT.PhysicalSpeciesCopySurplus.Realization.upEq => Physics.PhysicalSpeciesCopySurplus.Realization.upEq
