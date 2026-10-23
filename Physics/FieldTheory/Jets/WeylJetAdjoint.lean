import Physics.FieldTheory.Jets.Weyl.Equations.WeylJetAdjoint
import Physics.FieldTheory.Jets.ConjugateWeylEquation
import Math.Algebra.JetExteriorAdjoint
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylJetAdjoint instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylJetAdjoint.Algebra => Physics.WeylJetAdjoint.Algebra,
  GUT.WeylJetAdjoint.IBP => Physics.WeylJetAdjoint.IBP,
  GUT.WeylJetAdjoint.Paired => Physics.WeylJetAdjoint.Paired,
  GUT.WeylJetAdjoint.Source => Physics.WeylJetAdjoint.Source,
  GUT.WeylJetAdjoint.action => Physics.WeylJetAdjoint.action,
  GUT.WeylJetAdjoint.adjoint => Physics.WeylJetAdjoint.adjoint,
  GUT.WeylJetAdjoint.adjoint_action => Physics.WeylJetAdjoint.adjoint_action,
  GUT.WeylJetAdjoint.adjoint_derivative => Physics.WeylJetAdjoint.adjoint_derivative,
  GUT.WeylJetAdjoint.adjoint_generator => Physics.WeylJetAdjoint.adjoint_generator,
  GUT.WeylJetAdjoint.adjoint_ibp => Physics.WeylJetAdjoint.adjoint_ibp,
  GUT.WeylJetAdjoint.adjoint_involutive => Physics.WeylJetAdjoint.adjoint_involutive,
  GUT.WeylJetAdjoint.adjoint_mul => Physics.WeylJetAdjoint.adjoint_mul,
  GUT.WeylJetAdjoint.algebraProjection => Physics.WeylJetAdjoint.algebraProjection,
  GUT.WeylJetAdjoint.algebraProjection.eq_1 => Physics.WeylJetAdjoint.algebraProjection.eq_1,
  GUT.WeylJetAdjoint.algebraProjection_adjoint => Physics.WeylJetAdjoint.algebraProjection_adjoint,
  GUT.WeylJetAdjoint.algebraProjection_surjective => Physics.WeylJetAdjoint.algebraProjection_surjective,
  GUT.WeylJetAdjoint.conjugation => Physics.WeylJetAdjoint.conjugation,
  GUT.WeylJetAdjoint.conjugation_action => Physics.WeylJetAdjoint.conjugation_action,
  GUT.WeylJetAdjoint.conjugation_involutive => Physics.WeylJetAdjoint.conjugation_involutive,
  GUT.WeylJetAdjoint.conjugation_shift => Physics.WeylJetAdjoint.conjugation_shift,
  GUT.WeylJetAdjoint.derivative => Physics.WeylJetAdjoint.derivative,
  GUT.WeylJetAdjoint.derivative_commute => Physics.WeylJetAdjoint.derivative_commute,
  GUT.WeylJetAdjoint.left_descendant_zero => Physics.WeylJetAdjoint.left_descendant_zero,
  GUT.WeylJetAdjoint.projection => Physics.WeylJetAdjoint.projection,
  GUT.WeylJetAdjoint.projection_conjugation => Physics.WeylJetAdjoint.projection_conjugation,
  GUT.WeylJetAdjoint.projection_surjective => Physics.WeylJetAdjoint.projection_surjective,
  GUT.WeylJetAdjoint.rawConjugation => Physics.WeylJetAdjoint.rawConjugation,
  GUT.WeylJetAdjoint.right_descendant_zero => Physics.WeylJetAdjoint.right_descendant_zero,
  GUT.WeylJetAdjoint.shift => Physics.WeylJetAdjoint.shift,
  GUT.WeylJetAdjoint.shift_commute => Physics.WeylJetAdjoint.shift_commute,
  GUT.WeylJetAdjoint.sourceAdjoint => Physics.WeylJetAdjoint.sourceAdjoint,
  GUT.WeylJetAdjoint.sourceAdjoint_involutive => Physics.WeylJetAdjoint.sourceAdjoint_involutive,
  GUT.WeylJetAdjoint.sourceAdjoint_mk => Physics.WeylJetAdjoint.sourceAdjoint_mk
]

assert_compatible GUT.WeylJetAdjoint.Algebra => Physics.WeylJetAdjoint.Algebra
assert_compatible GUT.WeylJetAdjoint.IBP => Physics.WeylJetAdjoint.IBP
assert_compatible GUT.WeylJetAdjoint.Paired => Physics.WeylJetAdjoint.Paired
assert_compatible GUT.WeylJetAdjoint.Source => Physics.WeylJetAdjoint.Source
assert_compatible GUT.WeylJetAdjoint.action => Physics.WeylJetAdjoint.action
assert_compatible GUT.WeylJetAdjoint.adjoint => Physics.WeylJetAdjoint.adjoint
assert_compatible GUT.WeylJetAdjoint.adjoint_action => Physics.WeylJetAdjoint.adjoint_action
assert_compatible GUT.WeylJetAdjoint.adjoint_derivative => Physics.WeylJetAdjoint.adjoint_derivative
assert_compatible GUT.WeylJetAdjoint.adjoint_generator => Physics.WeylJetAdjoint.adjoint_generator
assert_compatible GUT.WeylJetAdjoint.adjoint_ibp => Physics.WeylJetAdjoint.adjoint_ibp
assert_compatible GUT.WeylJetAdjoint.adjoint_involutive => Physics.WeylJetAdjoint.adjoint_involutive
assert_compatible GUT.WeylJetAdjoint.adjoint_mul => Physics.WeylJetAdjoint.adjoint_mul
assert_compatible GUT.WeylJetAdjoint.algebraProjection => Physics.WeylJetAdjoint.algebraProjection
assert_compatible GUT.WeylJetAdjoint.algebraProjection.eq_1 => Physics.WeylJetAdjoint.algebraProjection.eq_1
assert_compatible GUT.WeylJetAdjoint.algebraProjection_adjoint => Physics.WeylJetAdjoint.algebraProjection_adjoint
assert_compatible GUT.WeylJetAdjoint.algebraProjection_surjective => Physics.WeylJetAdjoint.algebraProjection_surjective
assert_compatible GUT.WeylJetAdjoint.conjugation => Physics.WeylJetAdjoint.conjugation
assert_compatible GUT.WeylJetAdjoint.conjugation_action => Physics.WeylJetAdjoint.conjugation_action
assert_compatible GUT.WeylJetAdjoint.conjugation_involutive => Physics.WeylJetAdjoint.conjugation_involutive
assert_compatible GUT.WeylJetAdjoint.conjugation_shift => Physics.WeylJetAdjoint.conjugation_shift
assert_compatible GUT.WeylJetAdjoint.derivative => Physics.WeylJetAdjoint.derivative
assert_compatible GUT.WeylJetAdjoint.derivative_commute => Physics.WeylJetAdjoint.derivative_commute
assert_compatible GUT.WeylJetAdjoint.left_descendant_zero => Physics.WeylJetAdjoint.left_descendant_zero
assert_compatible GUT.WeylJetAdjoint.projection => Physics.WeylJetAdjoint.projection
assert_compatible GUT.WeylJetAdjoint.projection_conjugation => Physics.WeylJetAdjoint.projection_conjugation
assert_compatible GUT.WeylJetAdjoint.projection_surjective => Physics.WeylJetAdjoint.projection_surjective
assert_compatible GUT.WeylJetAdjoint.rawConjugation => Physics.WeylJetAdjoint.rawConjugation
assert_compatible GUT.WeylJetAdjoint.right_descendant_zero => Physics.WeylJetAdjoint.right_descendant_zero
assert_compatible GUT.WeylJetAdjoint.shift => Physics.WeylJetAdjoint.shift
assert_compatible GUT.WeylJetAdjoint.shift_commute => Physics.WeylJetAdjoint.shift_commute
assert_compatible GUT.WeylJetAdjoint.sourceAdjoint => Physics.WeylJetAdjoint.sourceAdjoint
assert_compatible GUT.WeylJetAdjoint.sourceAdjoint_involutive => Physics.WeylJetAdjoint.sourceAdjoint_involutive
assert_compatible GUT.WeylJetAdjoint.sourceAdjoint_mk => Physics.WeylJetAdjoint.sourceAdjoint_mk
