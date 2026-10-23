import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoModelInterface
import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Physics.StandardModel.Operators.DeltaBTwoLocalOperator
import Math.RepresentationTheory.SixSlotSpeciesTransport
import Math.RepresentationTheory.SixSlotRestrictionLift
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoModelInterface instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoModelInterface.Inputs => Physics.DeltaBTwoModelInterface.Inputs,
  GUT.DeltaBTwoModelInterface.Inputs.casesOn => Physics.DeltaBTwoModelInterface.Inputs.casesOn,
  GUT.DeltaBTwoModelInterface.Inputs.ctorIdx => Physics.DeltaBTwoModelInterface.Inputs.ctorIdx,
  GUT.DeltaBTwoModelInterface.Inputs.downEquiv => Physics.DeltaBTwoModelInterface.Inputs.downEquiv,
  GUT.DeltaBTwoModelInterface.Inputs.mk => Physics.DeltaBTwoModelInterface.Inputs.mk,
  GUT.DeltaBTwoModelInterface.Inputs.mk.inj => Physics.DeltaBTwoModelInterface.Inputs.mk.inj,
  GUT.DeltaBTwoModelInterface.Inputs.mk.injEq => Physics.DeltaBTwoModelInterface.Inputs.mk.injEq,
  GUT.DeltaBTwoModelInterface.Inputs.mk.noConfusion => Physics.DeltaBTwoModelInterface.Inputs.mk.noConfusion,
  GUT.DeltaBTwoModelInterface.Inputs.mk.sizeOf_spec => Physics.DeltaBTwoModelInterface.Inputs.mk.sizeOf_spec,
  GUT.DeltaBTwoModelInterface.Inputs.noConfusion => Physics.DeltaBTwoModelInterface.Inputs.noConfusion,
  GUT.DeltaBTwoModelInterface.Inputs.noConfusionType => Physics.DeltaBTwoModelInterface.Inputs.noConfusionType,
  GUT.DeltaBTwoModelInterface.Inputs.rec => Physics.DeltaBTwoModelInterface.Inputs.rec,
  GUT.DeltaBTwoModelInterface.Inputs.recOn => Physics.DeltaBTwoModelInterface.Inputs.recOn,
  GUT.DeltaBTwoModelInterface.Inputs.upEquiv => Physics.DeltaBTwoModelInterface.Inputs.upEquiv,
  GUT.DeltaBTwoModelInterface.ModelSector => Physics.DeltaBTwoModelInterface.ModelSector,
  GUT.DeltaBTwoModelInterface.OrderedCoefficient => Physics.DeltaBTwoModelInterface.OrderedCoefficient,
  GUT.DeltaBTwoModelInterface.SymmetryGroup => Physics.DeltaBTwoModelInterface.SymmetryGroup,
  GUT.DeltaBTwoModelInterface.downModel => Physics.DeltaBTwoModelInterface.downModel,
  GUT.DeltaBTwoModelInterface.exists_on_fields_iff => Physics.DeltaBTwoModelInterface.exists_on_fields_iff,
  GUT.DeltaBTwoModelInterface.exists_ordered => Physics.DeltaBTwoModelInterface.exists_ordered,
  GUT.DeltaBTwoModelInterface.onFieldsEquiv => Physics.DeltaBTwoModelInterface.onFieldsEquiv,
  GUT.DeltaBTwoModelInterface.species_baryon_grade => Physics.DeltaBTwoModelInterface.species_baryon_grade,
  GUT.DeltaBTwoModelInterface.upModel => Physics.DeltaBTwoModelInterface.upModel
]

assert_compatible GUT.DeltaBTwoModelInterface.Inputs => Physics.DeltaBTwoModelInterface.Inputs
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.casesOn => Physics.DeltaBTwoModelInterface.Inputs.casesOn
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.ctorIdx => Physics.DeltaBTwoModelInterface.Inputs.ctorIdx
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.downEquiv => Physics.DeltaBTwoModelInterface.Inputs.downEquiv
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.mk => Physics.DeltaBTwoModelInterface.Inputs.mk
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.mk.inj => Physics.DeltaBTwoModelInterface.Inputs.mk.inj
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.mk.injEq => Physics.DeltaBTwoModelInterface.Inputs.mk.injEq
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.mk.noConfusion => Physics.DeltaBTwoModelInterface.Inputs.mk.noConfusion
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.mk.sizeOf_spec => Physics.DeltaBTwoModelInterface.Inputs.mk.sizeOf_spec
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.noConfusion => Physics.DeltaBTwoModelInterface.Inputs.noConfusion
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.noConfusionType => Physics.DeltaBTwoModelInterface.Inputs.noConfusionType
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.rec => Physics.DeltaBTwoModelInterface.Inputs.rec
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.recOn => Physics.DeltaBTwoModelInterface.Inputs.recOn
assert_compatible GUT.DeltaBTwoModelInterface.Inputs.upEquiv => Physics.DeltaBTwoModelInterface.Inputs.upEquiv
assert_compatible GUT.DeltaBTwoModelInterface.ModelSector => Physics.DeltaBTwoModelInterface.ModelSector
assert_compatible GUT.DeltaBTwoModelInterface.OrderedCoefficient => Physics.DeltaBTwoModelInterface.OrderedCoefficient
assert_compatible GUT.DeltaBTwoModelInterface.SymmetryGroup => Physics.DeltaBTwoModelInterface.SymmetryGroup
assert_compatible GUT.DeltaBTwoModelInterface.downModel => Physics.DeltaBTwoModelInterface.downModel
assert_compatible GUT.DeltaBTwoModelInterface.exists_on_fields_iff => Physics.DeltaBTwoModelInterface.exists_on_fields_iff
assert_compatible GUT.DeltaBTwoModelInterface.exists_ordered => Physics.DeltaBTwoModelInterface.exists_ordered
assert_compatible GUT.DeltaBTwoModelInterface.onFieldsEquiv => Physics.DeltaBTwoModelInterface.onFieldsEquiv
assert_compatible GUT.DeltaBTwoModelInterface.species_baryon_grade => Physics.DeltaBTwoModelInterface.species_baryon_grade
assert_compatible GUT.DeltaBTwoModelInterface.upModel => Physics.DeltaBTwoModelInterface.upModel
