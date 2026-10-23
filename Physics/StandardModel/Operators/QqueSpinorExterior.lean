import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.ExplicitSMResidualTensor
import Math.RepresentationTheory.SymmetricInvariantPairing
import Math.RepresentationTheory.FourSlotAlternation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueSpinorExterior.ExteriorCoefficient => Physics.QqueSpinorExterior.ExteriorCoefficient,
  GUT.QqueSpinorExterior.HasModelExterior => Physics.QqueSpinorExterior.HasModelExterior,
  GUT.QqueSpinorExterior.HasNonzeroAlternation => Physics.QqueSpinorExterior.HasNonzeroAlternation,
  GUT.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior => Physics.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior,
  GUT.QqueSpinorExterior.OrderedCoefficient => Physics.QqueSpinorExterior.OrderedCoefficient,
  GUT.QqueSpinorExterior.eField => Physics.QqueSpinorExterior.eField,
  GUT.QqueSpinorExterior.eSpin => Physics.QqueSpinorExterior.eSpin,
  GUT.QqueSpinorExterior.exists_on_fields => Physics.QqueSpinorExterior.exists_on_fields,
  GUT.QqueSpinorExterior.exterior => Physics.QqueSpinorExterior.exterior,
  GUT.QqueSpinorExterior.exterior.eq_1 => Physics.QqueSpinorExterior.exterior.eq_1,
  GUT.QqueSpinorExterior.fullAction => Physics.QqueSpinorExterior.fullAction,
  GUT.QqueSpinorExterior.hasModelExterior => Physics.QqueSpinorExterior.hasModelExterior,
  GUT.QqueSpinorExterior.instAddCommGroupQuark => Physics.QqueSpinorExterior.instAddCommGroupQuark,
  GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexColorDualSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexColorDualSpace,
  GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexDualSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexDualSpace,
  GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuark => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuark,
  GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuarkSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuarkSpace,
  GUT.QqueSpinorExterior.internal => Physics.QqueSpinorExterior.internal,
  GUT.QqueSpinorExterior.internal.eq_1 => Physics.QqueSpinorExterior.internal.eq_1,
  GUT.QqueSpinorExterior.matched => Physics.QqueSpinorExterior.matched,
  GUT.QqueSpinorExterior.matched.eq_1 => Physics.QqueSpinorExterior.matched.eq_1,
  GUT.QqueSpinorExterior.matched_diagonal => Physics.QqueSpinorExterior.matched_diagonal,
  GUT.QqueSpinorExterior.matched_nonzero => Physics.QqueSpinorExterior.matched_nonzero,
  GUT.QqueSpinorExterior.ordered => Physics.QqueSpinorExterior.ordered,
  GUT.QqueSpinorExterior.ordered_apply => Physics.QqueSpinorExterior.ordered_apply,
  GUT.QqueSpinorExterior.qField => Physics.QqueSpinorExterior.qField,
  GUT.QqueSpinorExterior.qSpin => Physics.QqueSpinorExterior.qSpin,
  GUT.QqueSpinorExterior.uField => Physics.QqueSpinorExterior.uField,
  GUT.QqueSpinorExterior.uSpin => Physics.QqueSpinorExterior.uSpin
]

assert_compatible GUT.QqueSpinorExterior.ExteriorCoefficient => Physics.QqueSpinorExterior.ExteriorCoefficient
assert_compatible GUT.QqueSpinorExterior.HasModelExterior => Physics.QqueSpinorExterior.HasModelExterior
assert_compatible GUT.QqueSpinorExterior.HasNonzeroAlternation => Physics.QqueSpinorExterior.HasNonzeroAlternation
assert_compatible GUT.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior => Physics.QqueSpinorExterior.HasNonzeroAlternation.exists_exterior
assert_compatible GUT.QqueSpinorExterior.OrderedCoefficient => Physics.QqueSpinorExterior.OrderedCoefficient
assert_compatible GUT.QqueSpinorExterior.eField => Physics.QqueSpinorExterior.eField
assert_compatible GUT.QqueSpinorExterior.eSpin => Physics.QqueSpinorExterior.eSpin
assert_compatible GUT.QqueSpinorExterior.exists_on_fields => Physics.QqueSpinorExterior.exists_on_fields
assert_compatible GUT.QqueSpinorExterior.exterior => Physics.QqueSpinorExterior.exterior
assert_compatible GUT.QqueSpinorExterior.exterior.eq_1 => Physics.QqueSpinorExterior.exterior.eq_1
assert_compatible GUT.QqueSpinorExterior.fullAction => Physics.QqueSpinorExterior.fullAction
assert_compatible GUT.QqueSpinorExterior.hasModelExterior => Physics.QqueSpinorExterior.hasModelExterior
assert_compatible GUT.QqueSpinorExterior.instAddCommGroupQuark => Physics.QqueSpinorExterior.instAddCommGroupQuark
assert_compatible GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexColorDualSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexColorDualSpace
assert_compatible GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexDualSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexDualSpace
assert_compatible GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuark => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuark
assert_compatible GUT.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuarkSpace => Physics.QqueSpinorExterior.instAddCommGroupTensorProductComplexQuarkSpace
assert_compatible GUT.QqueSpinorExterior.internal => Physics.QqueSpinorExterior.internal
assert_compatible GUT.QqueSpinorExterior.internal.eq_1 => Physics.QqueSpinorExterior.internal.eq_1
assert_compatible GUT.QqueSpinorExterior.matched => Physics.QqueSpinorExterior.matched
assert_compatible GUT.QqueSpinorExterior.matched.eq_1 => Physics.QqueSpinorExterior.matched.eq_1
assert_compatible GUT.QqueSpinorExterior.matched_diagonal => Physics.QqueSpinorExterior.matched_diagonal
assert_compatible GUT.QqueSpinorExterior.matched_nonzero => Physics.QqueSpinorExterior.matched_nonzero
assert_compatible GUT.QqueSpinorExterior.ordered => Physics.QqueSpinorExterior.ordered
assert_compatible GUT.QqueSpinorExterior.ordered_apply => Physics.QqueSpinorExterior.ordered_apply
assert_compatible GUT.QqueSpinorExterior.qField => Physics.QqueSpinorExterior.qField
assert_compatible GUT.QqueSpinorExterior.qSpin => Physics.QqueSpinorExterior.qSpin
assert_compatible GUT.QqueSpinorExterior.uField => Physics.QqueSpinorExterior.uField
assert_compatible GUT.QqueSpinorExterior.uSpin => Physics.QqueSpinorExterior.uSpin
