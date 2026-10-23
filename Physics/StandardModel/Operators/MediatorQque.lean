import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQque
import Math.LinearAlgebra.MediatorExchange
import Math.RepresentationTheory.InvariantPairing
import Math.RepresentationTheory.OrderedInvariantPairing
import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MediatorQque.IsInvariant => Physics.MediatorQque.IsInvariant,
  GUT.MediatorQque.equivariantInternal => Physics.MediatorQque.equivariantInternal,
  GUT.MediatorQque.equivariantInternal_linear => Physics.MediatorQque.equivariantInternal_linear,
  GUT.MediatorQque.hom => Physics.MediatorQque.hom,
  GUT.MediatorQque.hom_eq_zero_iff => Physics.MediatorQque.hom_eq_zero_iff,
  GUT.MediatorQque.hom_ne_zero_iff => Physics.MediatorQque.hom_ne_zero_iff,
  GUT.MediatorQque.instAddCommGroupQuark => Physics.MediatorQque.instAddCommGroupQuark,
  GUT.MediatorQque.instAddCommGroupTensorProductComplexColorDual => Physics.MediatorQque.instAddCommGroupTensorProductComplexColorDual,
  GUT.MediatorQque.instAddCommGroupTensorProductComplexDual_physics => Physics.MediatorQque.instAddCommGroupTensorProductComplexDual_physics,
  GUT.MediatorQque.instAddCommGroupTensorProductComplexQuark => Physics.MediatorQque.instAddCommGroupTensorProductComplexQuark,
  GUT.MediatorQque.internal => Physics.MediatorQque.internal,
  GUT.MediatorQque.invariant_of_equivariant => Physics.MediatorQque.invariant_of_equivariant,
  GUT.MediatorQque.ordered_eq_action => Physics.MediatorQque.ordered_eq_action,
  GUT.MediatorQque.reconstruct => Physics.MediatorQque.reconstruct,
  GUT.MediatorQque.sector => Physics.MediatorQque.sector
]

assert_compatible GUT.MediatorQque.IsInvariant => Physics.MediatorQque.IsInvariant
assert_compatible GUT.MediatorQque.equivariantInternal => Physics.MediatorQque.equivariantInternal
assert_compatible GUT.MediatorQque.equivariantInternal_linear => Physics.MediatorQque.equivariantInternal_linear
assert_compatible GUT.MediatorQque.hom => Physics.MediatorQque.hom
assert_compatible GUT.MediatorQque.hom_eq_zero_iff => Physics.MediatorQque.hom_eq_zero_iff
assert_compatible GUT.MediatorQque.hom_ne_zero_iff => Physics.MediatorQque.hom_ne_zero_iff
assert_compatible GUT.MediatorQque.instAddCommGroupQuark => Physics.MediatorQque.instAddCommGroupQuark
assert_compatible GUT.MediatorQque.instAddCommGroupTensorProductComplexColorDual => Physics.MediatorQque.instAddCommGroupTensorProductComplexColorDual
assert_compatible GUT.MediatorQque.instAddCommGroupTensorProductComplexDual_physics => Physics.MediatorQque.instAddCommGroupTensorProductComplexDual_physics
assert_compatible GUT.MediatorQque.instAddCommGroupTensorProductComplexQuark => Physics.MediatorQque.instAddCommGroupTensorProductComplexQuark
assert_compatible GUT.MediatorQque.internal => Physics.MediatorQque.internal
assert_compatible GUT.MediatorQque.invariant_of_equivariant => Physics.MediatorQque.invariant_of_equivariant
assert_compatible GUT.MediatorQque.ordered_eq_action => Physics.MediatorQque.ordered_eq_action
assert_compatible GUT.MediatorQque.reconstruct => Physics.MediatorQque.reconstruct
assert_compatible GUT.MediatorQque.sector => Physics.MediatorQque.sector
