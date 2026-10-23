import Physics.StandardModel.Operators.Support.Quark.SMQ18Support
import Physics.StandardModel.Operators.SMGenerationSupport
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Math.RepresentationTheory.SelfDualCoefficient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQ18Support instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQ18Support.Field => Physics.SMQ18Support.Field,
  GUT.SMQ18Support.PresentedField => Physics.SMQ18Support.PresentedField,
  GUT.SMQ18Support.PresentedField.action => Physics.SMQ18Support.PresentedField.action,
  GUT.SMQ18Support.PresentedField.addEquiv => Physics.SMQ18Support.PresentedField.addEquiv,
  GUT.SMQ18Support.PresentedField.casesOn => Physics.SMQ18Support.PresentedField.casesOn,
  GUT.SMQ18Support.PresentedField.ctorIdx => Physics.SMQ18Support.PresentedField.ctorIdx,
  GUT.SMQ18Support.PresentedField.determinant => Physics.SMQ18Support.PresentedField.determinant,
  GUT.SMQ18Support.PresentedField.dimension => Physics.SMQ18Support.PresentedField.dimension,
  GUT.SMQ18Support.PresentedField.equiv => Physics.SMQ18Support.PresentedField.equiv,
  GUT.SMQ18Support.PresentedField.instAddCommGroup => Physics.SMQ18Support.PresentedField.instAddCommGroup,
  GUT.SMQ18Support.PresentedField.instFiniteDimensionalComplex => Physics.SMQ18Support.PresentedField.instFiniteDimensionalComplex,
  GUT.SMQ18Support.PresentedField.instModuleComplex => Physics.SMQ18Support.PresentedField.instModuleComplex,
  GUT.SMQ18Support.PresentedField.linearEquiv => Physics.SMQ18Support.PresentedField.linearEquiv,
  GUT.SMQ18Support.PresentedField.middleDuality => Physics.SMQ18Support.PresentedField.middleDuality,
  GUT.SMQ18Support.PresentedField.mk => Physics.SMQ18Support.PresentedField.mk,
  GUT.SMQ18Support.PresentedField.mk.inj => Physics.SMQ18Support.PresentedField.mk.inj,
  GUT.SMQ18Support.PresentedField.mk.injEq => Physics.SMQ18Support.PresentedField.mk.injEq,
  GUT.SMQ18Support.PresentedField.mk.noConfusion => Physics.SMQ18Support.PresentedField.mk.noConfusion,
  GUT.SMQ18Support.PresentedField.mk.sizeOf_spec => Physics.SMQ18Support.PresentedField.mk.sizeOf_spec,
  GUT.SMQ18Support.PresentedField.noConfusion => Physics.SMQ18Support.PresentedField.noConfusion,
  GUT.SMQ18Support.PresentedField.noConfusionType => Physics.SMQ18Support.PresentedField.noConfusionType,
  GUT.SMQ18Support.PresentedField.rec => Physics.SMQ18Support.PresentedField.rec,
  GUT.SMQ18Support.PresentedField.recOn => Physics.SMQ18Support.PresentedField.recOn,
  GUT.SMQ18Support.PresentedField.representationEquiv => Physics.SMQ18Support.PresentedField.representationEquiv,
  GUT.SMQ18Support.PresentedField.val => Physics.SMQ18Support.PresentedField.val,
  GUT.SMQ18Support.actualFieldEquiv => Physics.SMQ18Support.actualFieldEquiv,
  GUT.SMQ18Support.actualQuarkEquiv => Physics.SMQ18Support.actualQuarkEquiv,
  GUT.SMQ18Support.field_det => Physics.SMQ18Support.field_det,
  GUT.SMQ18Support.field_dimension => Physics.SMQ18Support.field_dimension,
  GUT.SMQ18Support.instAddCommGroupField => Physics.SMQ18Support.instAddCommGroupField,
  GUT.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet,
  GUT.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet_1,
  GUT.SMQ18Support.middleDuality => Physics.SMQ18Support.middleDuality,
  GUT.SMQ18Support.rho => Physics.SMQ18Support.rho,
  GUT.SMQ18Support.semisimple_allowed => Physics.SMQ18Support.semisimple_allowed,
  GUT.SMQ18Support.weak_det => Physics.SMQ18Support.weak_det
]

assert_compatible GUT.SMQ18Support.Field => Physics.SMQ18Support.Field
assert_compatible GUT.SMQ18Support.PresentedField => Physics.SMQ18Support.PresentedField
assert_compatible GUT.SMQ18Support.PresentedField.action => Physics.SMQ18Support.PresentedField.action
assert_compatible GUT.SMQ18Support.PresentedField.addEquiv => Physics.SMQ18Support.PresentedField.addEquiv
assert_compatible GUT.SMQ18Support.PresentedField.casesOn => Physics.SMQ18Support.PresentedField.casesOn
assert_compatible GUT.SMQ18Support.PresentedField.ctorIdx => Physics.SMQ18Support.PresentedField.ctorIdx
assert_compatible GUT.SMQ18Support.PresentedField.determinant => Physics.SMQ18Support.PresentedField.determinant
assert_compatible GUT.SMQ18Support.PresentedField.dimension => Physics.SMQ18Support.PresentedField.dimension
assert_compatible GUT.SMQ18Support.PresentedField.equiv => Physics.SMQ18Support.PresentedField.equiv
assert_compatible GUT.SMQ18Support.PresentedField.instAddCommGroup => Physics.SMQ18Support.PresentedField.instAddCommGroup
assert_compatible GUT.SMQ18Support.PresentedField.instFiniteDimensionalComplex => Physics.SMQ18Support.PresentedField.instFiniteDimensionalComplex
assert_compatible GUT.SMQ18Support.PresentedField.instModuleComplex => Physics.SMQ18Support.PresentedField.instModuleComplex
assert_compatible GUT.SMQ18Support.PresentedField.linearEquiv => Physics.SMQ18Support.PresentedField.linearEquiv
assert_compatible GUT.SMQ18Support.PresentedField.middleDuality => Physics.SMQ18Support.PresentedField.middleDuality
assert_compatible GUT.SMQ18Support.PresentedField.mk => Physics.SMQ18Support.PresentedField.mk
assert_compatible GUT.SMQ18Support.PresentedField.mk.inj => Physics.SMQ18Support.PresentedField.mk.inj
assert_compatible GUT.SMQ18Support.PresentedField.mk.injEq => Physics.SMQ18Support.PresentedField.mk.injEq
assert_compatible GUT.SMQ18Support.PresentedField.mk.noConfusion => Physics.SMQ18Support.PresentedField.mk.noConfusion
assert_compatible GUT.SMQ18Support.PresentedField.mk.sizeOf_spec => Physics.SMQ18Support.PresentedField.mk.sizeOf_spec
assert_compatible GUT.SMQ18Support.PresentedField.noConfusion => Physics.SMQ18Support.PresentedField.noConfusion
assert_compatible GUT.SMQ18Support.PresentedField.noConfusionType => Physics.SMQ18Support.PresentedField.noConfusionType
assert_compatible GUT.SMQ18Support.PresentedField.rec => Physics.SMQ18Support.PresentedField.rec
assert_compatible GUT.SMQ18Support.PresentedField.recOn => Physics.SMQ18Support.PresentedField.recOn
assert_compatible GUT.SMQ18Support.PresentedField.representationEquiv => Physics.SMQ18Support.PresentedField.representationEquiv
assert_compatible GUT.SMQ18Support.PresentedField.val => Physics.SMQ18Support.PresentedField.val
assert_compatible GUT.SMQ18Support.actualFieldEquiv => Physics.SMQ18Support.actualFieldEquiv
assert_compatible GUT.SMQ18Support.actualQuarkEquiv => Physics.SMQ18Support.actualQuarkEquiv
assert_compatible GUT.SMQ18Support.field_det => Physics.SMQ18Support.field_det
assert_compatible GUT.SMQ18Support.field_dimension => Physics.SMQ18Support.field_dimension
assert_compatible GUT.SMQ18Support.instAddCommGroupField => Physics.SMQ18Support.instAddCommGroupField
assert_compatible GUT.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet => Physics.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet
assert_compatible GUT.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet_1 => Physics.SMQ18Support.instAddCommGroupTensorProductComplexColorDoublet_1
assert_compatible GUT.SMQ18Support.middleDuality => Physics.SMQ18Support.middleDuality
assert_compatible GUT.SMQ18Support.rho => Physics.SMQ18Support.rho
assert_compatible GUT.SMQ18Support.semisimple_allowed => Physics.SMQ18Support.semisimple_allowed
assert_compatible GUT.SMQ18Support.weak_det => Physics.SMQ18Support.weak_det
