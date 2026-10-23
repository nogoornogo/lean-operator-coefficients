import Physics.StandardModel.Operators.Support.Quark.SMColoredCoreBranching
import Math.RepresentationTheory.SU3SpinExterior
import Math.RepresentationTheory.SU3ConjugateSpinExterior
import Physics.StandardModel.Operators.SMGenerationExhaustion
import Physics.StandardModel.Operators.SMGenerationCauchy
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMColoredCoreBranching instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMColoredCoreBranching.actual_conjugateDown => Physics.SMColoredCoreBranching.actual_conjugateDown,
  GUT.SMColoredCoreBranching.actual_conjugateUp => Physics.SMColoredCoreBranching.actual_conjugateUp,
  GUT.SMColoredCoreBranching.actual_down => Physics.SMColoredCoreBranching.actual_down,
  GUT.SMColoredCoreBranching.actual_up => Physics.SMColoredCoreBranching.actual_up,
  GUT.SMColoredCoreBranching.core => Physics.SMColoredCoreBranching.core,
  GUT.SMColoredCoreBranching.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredCoreBranching.instAddCommGroupTensorProductComplex_physics,
  GUT.SMColoredCoreBranching.negativeEquiv => Physics.SMColoredCoreBranching.negativeEquiv,
  GUT.SMColoredCoreBranching.negativeExteriorEquiv => Physics.SMColoredCoreBranching.negativeExteriorEquiv,
  GUT.SMColoredCoreBranching.negativeFour => Physics.SMColoredCoreBranching.negativeFour,
  GUT.SMColoredCoreBranching.negativeSquare => Physics.SMColoredCoreBranching.negativeSquare,
  GUT.SMColoredCoreBranching.positiveEquiv => Physics.SMColoredCoreBranching.positiveEquiv,
  GUT.SMColoredCoreBranching.positiveExteriorEquiv => Physics.SMColoredCoreBranching.positiveExteriorEquiv,
  GUT.SMColoredCoreBranching.positiveFour => Physics.SMColoredCoreBranching.positiveFour,
  GUT.SMColoredCoreBranching.positiveSquare => Physics.SMColoredCoreBranching.positiveSquare,
  GUT.SMColoredCoreBranching.projection => Physics.SMColoredCoreBranching.projection,
  GUT.SMColoredCoreBranching.projection.eq_1 => Physics.SMColoredCoreBranching.projection.eq_1,
  GUT.SMColoredCoreBranching.projection_surjective => Physics.SMColoredCoreBranching.projection_surjective
]

assert_compatible GUT.SMColoredCoreBranching.actual_conjugateDown => Physics.SMColoredCoreBranching.actual_conjugateDown
assert_compatible GUT.SMColoredCoreBranching.actual_conjugateUp => Physics.SMColoredCoreBranching.actual_conjugateUp
assert_compatible GUT.SMColoredCoreBranching.actual_down => Physics.SMColoredCoreBranching.actual_down
assert_compatible GUT.SMColoredCoreBranching.actual_up => Physics.SMColoredCoreBranching.actual_up
assert_compatible GUT.SMColoredCoreBranching.core => Physics.SMColoredCoreBranching.core
assert_compatible GUT.SMColoredCoreBranching.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredCoreBranching.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMColoredCoreBranching.negativeEquiv => Physics.SMColoredCoreBranching.negativeEquiv
assert_compatible GUT.SMColoredCoreBranching.negativeExteriorEquiv => Physics.SMColoredCoreBranching.negativeExteriorEquiv
assert_compatible GUT.SMColoredCoreBranching.negativeFour => Physics.SMColoredCoreBranching.negativeFour
assert_compatible GUT.SMColoredCoreBranching.negativeSquare => Physics.SMColoredCoreBranching.negativeSquare
assert_compatible GUT.SMColoredCoreBranching.positiveEquiv => Physics.SMColoredCoreBranching.positiveEquiv
assert_compatible GUT.SMColoredCoreBranching.positiveExteriorEquiv => Physics.SMColoredCoreBranching.positiveExteriorEquiv
assert_compatible GUT.SMColoredCoreBranching.positiveFour => Physics.SMColoredCoreBranching.positiveFour
assert_compatible GUT.SMColoredCoreBranching.positiveSquare => Physics.SMColoredCoreBranching.positiveSquare
assert_compatible GUT.SMColoredCoreBranching.projection => Physics.SMColoredCoreBranching.projection
assert_compatible GUT.SMColoredCoreBranching.projection.eq_1 => Physics.SMColoredCoreBranching.projection.eq_1
assert_compatible GUT.SMColoredCoreBranching.projection_surjective => Physics.SMColoredCoreBranching.projection_surjective
