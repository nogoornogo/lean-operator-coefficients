import Physics.FieldTheory.Jets.Weyl.Equations.ConjugateWeylEquation
import Physics.FieldTheory.Jets.WeylEquationControls
import Math.Algebra.JetConjugation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.ConjugateWeylEquation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConjugateWeylEquation.RightGenerator => Physics.ConjugateWeylEquation.RightGenerator,
  GUT.ConjugateWeylEquation.conjugate_relations => Physics.ConjugateWeylEquation.conjugate_relations,
  GUT.ConjugateWeylEquation.conjugate_relations_iff => Physics.ConjugateWeylEquation.conjugate_relations_iff,
  GUT.ConjugateWeylEquation.conjugate_right_relations => Physics.ConjugateWeylEquation.conjugate_right_relations,
  GUT.ConjugateWeylEquation.direction_real => Physics.ConjugateWeylEquation.direction_real,
  GUT.ConjugateWeylEquation.equationConjugation => Physics.ConjugateWeylEquation.equationConjugation,
  GUT.ConjugateWeylEquation.equationConjugation_apply => Physics.ConjugateWeylEquation.equationConjugation_apply,
  GUT.ConjugateWeylEquation.equationConjugation_involutive => Physics.ConjugateWeylEquation.equationConjugation_involutive,
  GUT.ConjugateWeylEquation.equationConjugation_row => Physics.ConjugateWeylEquation.equationConjugation_row,
  GUT.ConjugateWeylEquation.equation_action => Physics.ConjugateWeylEquation.equation_action,
  GUT.ConjugateWeylEquation.field_conjugation => Physics.ConjugateWeylEquation.field_conjugation,
  GUT.ConjugateWeylEquation.jet_conjugation => Physics.ConjugateWeylEquation.jet_conjugation,
  GUT.ConjugateWeylEquation.rightAction => Physics.ConjugateWeylEquation.rightAction,
  GUT.ConjugateWeylEquation.rightRelations => Physics.ConjugateWeylEquation.rightRelations,
  GUT.ConjugateWeylEquation.rightSeed => Physics.ConjugateWeylEquation.rightSeed,
  GUT.ConjugateWeylEquation.rightSeed.eq_1 => Physics.ConjugateWeylEquation.rightSeed.eq_1,
  GUT.ConjugateWeylEquation.rightSeed_covariant => Physics.ConjugateWeylEquation.rightSeed_covariant,
  GUT.ConjugateWeylEquation.rightSeed_row_one => Physics.ConjugateWeylEquation.rightSeed_row_one,
  GUT.ConjugateWeylEquation.rightSeed_row_zero => Physics.ConjugateWeylEquation.rightSeed_row_zero,
  GUT.ConjugateWeylEquation.right_higher_jet_survives => Physics.ConjugateWeylEquation.right_higher_jet_survives,
  GUT.ConjugateWeylEquation.spinor_conjugation => Physics.ConjugateWeylEquation.spinor_conjugation,
  GUT.ConjugateWeylEquation.toLeft => Physics.ConjugateWeylEquation.toLeft,
  GUT.ConjugateWeylEquation.toLeft_action => Physics.ConjugateWeylEquation.toLeft_action,
  GUT.ConjugateWeylEquation.toLeft_shift => Physics.ConjugateWeylEquation.toLeft_shift,
  GUT.ConjugateWeylEquation.toLeft_toRight => Physics.ConjugateWeylEquation.toLeft_toRight,
  GUT.ConjugateWeylEquation.toRight => Physics.ConjugateWeylEquation.toRight,
  GUT.ConjugateWeylEquation.toRight_action => Physics.ConjugateWeylEquation.toRight_action,
  GUT.ConjugateWeylEquation.toRight_shift => Physics.ConjugateWeylEquation.toRight_shift,
  GUT.ConjugateWeylEquation.toRight_toLeft => Physics.ConjugateWeylEquation.toRight_toLeft,
  GUT.WeylLinearEquation.row.eq_1 => Physics.WeylLinearEquation.row.eq_1
]

assert_compatible GUT.ConjugateWeylEquation.RightGenerator => Physics.ConjugateWeylEquation.RightGenerator
assert_compatible GUT.ConjugateWeylEquation.conjugate_relations => Physics.ConjugateWeylEquation.conjugate_relations
assert_compatible GUT.ConjugateWeylEquation.conjugate_relations_iff => Physics.ConjugateWeylEquation.conjugate_relations_iff
assert_compatible GUT.ConjugateWeylEquation.conjugate_right_relations => Physics.ConjugateWeylEquation.conjugate_right_relations
assert_compatible GUT.ConjugateWeylEquation.direction_real => Physics.ConjugateWeylEquation.direction_real
assert_compatible GUT.ConjugateWeylEquation.equationConjugation => Physics.ConjugateWeylEquation.equationConjugation
assert_compatible GUT.ConjugateWeylEquation.equationConjugation_apply => Physics.ConjugateWeylEquation.equationConjugation_apply
assert_compatible GUT.ConjugateWeylEquation.equationConjugation_involutive => Physics.ConjugateWeylEquation.equationConjugation_involutive
assert_compatible GUT.ConjugateWeylEquation.equationConjugation_row => Physics.ConjugateWeylEquation.equationConjugation_row
assert_compatible GUT.ConjugateWeylEquation.equation_action => Physics.ConjugateWeylEquation.equation_action
assert_compatible GUT.ConjugateWeylEquation.field_conjugation => Physics.ConjugateWeylEquation.field_conjugation
assert_compatible GUT.ConjugateWeylEquation.jet_conjugation => Physics.ConjugateWeylEquation.jet_conjugation
assert_compatible GUT.ConjugateWeylEquation.rightAction => Physics.ConjugateWeylEquation.rightAction
assert_compatible GUT.ConjugateWeylEquation.rightRelations => Physics.ConjugateWeylEquation.rightRelations
assert_compatible GUT.ConjugateWeylEquation.rightSeed => Physics.ConjugateWeylEquation.rightSeed
assert_compatible GUT.ConjugateWeylEquation.rightSeed.eq_1 => Physics.ConjugateWeylEquation.rightSeed.eq_1
assert_compatible GUT.ConjugateWeylEquation.rightSeed_covariant => Physics.ConjugateWeylEquation.rightSeed_covariant
assert_compatible GUT.ConjugateWeylEquation.rightSeed_row_one => Physics.ConjugateWeylEquation.rightSeed_row_one
assert_compatible GUT.ConjugateWeylEquation.rightSeed_row_zero => Physics.ConjugateWeylEquation.rightSeed_row_zero
assert_compatible GUT.ConjugateWeylEquation.right_higher_jet_survives => Physics.ConjugateWeylEquation.right_higher_jet_survives
assert_compatible GUT.ConjugateWeylEquation.spinor_conjugation => Physics.ConjugateWeylEquation.spinor_conjugation
assert_compatible GUT.ConjugateWeylEquation.toLeft => Physics.ConjugateWeylEquation.toLeft
assert_compatible GUT.ConjugateWeylEquation.toLeft_action => Physics.ConjugateWeylEquation.toLeft_action
assert_compatible GUT.ConjugateWeylEquation.toLeft_shift => Physics.ConjugateWeylEquation.toLeft_shift
assert_compatible GUT.ConjugateWeylEquation.toLeft_toRight => Physics.ConjugateWeylEquation.toLeft_toRight
assert_compatible GUT.ConjugateWeylEquation.toRight => Physics.ConjugateWeylEquation.toRight
assert_compatible GUT.ConjugateWeylEquation.toRight_action => Physics.ConjugateWeylEquation.toRight_action
assert_compatible GUT.ConjugateWeylEquation.toRight_shift => Physics.ConjugateWeylEquation.toRight_shift
assert_compatible GUT.ConjugateWeylEquation.toRight_toLeft => Physics.ConjugateWeylEquation.toRight_toLeft
assert_compatible GUT.WeylLinearEquation.row.eq_1 => Physics.WeylLinearEquation.row.eq_1
