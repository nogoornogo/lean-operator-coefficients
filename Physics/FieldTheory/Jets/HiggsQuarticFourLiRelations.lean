import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiRelations
import Math.RepresentationTheory.DerivativeLiteratureLiHiggs
import Physics.FieldTheory.Jets.HiggsQuarticFourReduction
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiRelations instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourLiRelations.B2_formula => Physics.HiggsQuarticFourLiRelations.B2_formula,
  GUT.HiggsQuarticFourLiRelations.C3_formula => Physics.HiggsQuarticFourLiRelations.C3_formula,
  GUT.HiggsQuarticFourLiRelations.adjoint_identity => Physics.HiggsQuarticFourLiRelations.adjoint_identity,
  GUT.HiggsQuarticFourLiRelations.box_add => Physics.HiggsQuarticFourLiRelations.box_add,
  GUT.HiggsQuarticFourLiRelations.box_adjoint => Physics.HiggsQuarticFourLiRelations.box_adjoint,
  GUT.HiggsQuarticFourLiRelations.box_commute => Physics.HiggsQuarticFourLiRelations.box_commute,
  GUT.HiggsQuarticFourLiRelations.box_left_mem => Physics.HiggsQuarticFourLiRelations.box_left_mem,
  GUT.HiggsQuarticFourLiRelations.box_rho_mem => Physics.HiggsQuarticFourLiRelations.box_rho_mem,
  GUT.HiggsQuarticFourLiRelations.box_sub => Physics.HiggsQuarticFourLiRelations.box_sub,
  GUT.HiggsQuarticFourLiRelations.l1_value => Physics.HiggsQuarticFourLiRelations.l1_value,
  GUT.HiggsQuarticFourLiRelations.l2_literal => Physics.HiggsQuarticFourLiRelations.l2_literal,
  GUT.HiggsQuarticFourLiRelations.l2_value => Physics.HiggsQuarticFourLiRelations.l2_value,
  GUT.HiggsQuarticFourLiRelations.l3_remainder => Physics.HiggsQuarticFourLiRelations.l3_remainder,
  GUT.HiggsQuarticFourLiRelations.l3_value => Physics.HiggsQuarticFourLiRelations.l3_value,
  GUT.HiggsQuarticFourLiRelations.pair_box_mem => Physics.HiggsQuarticFourLiRelations.pair_box_mem,
  GUT.HiggsQuarticFourLiRelations.pair_comm => Physics.HiggsQuarticFourLiRelations.pair_comm,
  GUT.HiggsQuarticFourLiRelations.reduced3 => Physics.HiggsQuarticFourLiRelations.reduced3,
  GUT.HiggsQuarticFourLiRelations.reduced3.eq_1 => Physics.HiggsQuarticFourLiRelations.reduced3.eq_1
]

assert_compatible GUT.HiggsQuarticFourLiRelations.B2_formula => Physics.HiggsQuarticFourLiRelations.B2_formula
assert_compatible GUT.HiggsQuarticFourLiRelations.C3_formula => Physics.HiggsQuarticFourLiRelations.C3_formula
assert_compatible GUT.HiggsQuarticFourLiRelations.adjoint_identity => Physics.HiggsQuarticFourLiRelations.adjoint_identity
assert_compatible GUT.HiggsQuarticFourLiRelations.box_add => Physics.HiggsQuarticFourLiRelations.box_add
assert_compatible GUT.HiggsQuarticFourLiRelations.box_adjoint => Physics.HiggsQuarticFourLiRelations.box_adjoint
assert_compatible GUT.HiggsQuarticFourLiRelations.box_commute => Physics.HiggsQuarticFourLiRelations.box_commute
assert_compatible GUT.HiggsQuarticFourLiRelations.box_left_mem => Physics.HiggsQuarticFourLiRelations.box_left_mem
assert_compatible GUT.HiggsQuarticFourLiRelations.box_rho_mem => Physics.HiggsQuarticFourLiRelations.box_rho_mem
assert_compatible GUT.HiggsQuarticFourLiRelations.box_sub => Physics.HiggsQuarticFourLiRelations.box_sub
assert_compatible GUT.HiggsQuarticFourLiRelations.l1_value => Physics.HiggsQuarticFourLiRelations.l1_value
assert_compatible GUT.HiggsQuarticFourLiRelations.l2_literal => Physics.HiggsQuarticFourLiRelations.l2_literal
assert_compatible GUT.HiggsQuarticFourLiRelations.l2_value => Physics.HiggsQuarticFourLiRelations.l2_value
assert_compatible GUT.HiggsQuarticFourLiRelations.l3_remainder => Physics.HiggsQuarticFourLiRelations.l3_remainder
assert_compatible GUT.HiggsQuarticFourLiRelations.l3_value => Physics.HiggsQuarticFourLiRelations.l3_value
assert_compatible GUT.HiggsQuarticFourLiRelations.pair_box_mem => Physics.HiggsQuarticFourLiRelations.pair_box_mem
assert_compatible GUT.HiggsQuarticFourLiRelations.pair_comm => Physics.HiggsQuarticFourLiRelations.pair_comm
assert_compatible GUT.HiggsQuarticFourLiRelations.reduced3 => Physics.HiggsQuarticFourLiRelations.reduced3
assert_compatible GUT.HiggsQuarticFourLiRelations.reduced3.eq_1 => Physics.HiggsQuarticFourLiRelations.reduced3.eq_1
