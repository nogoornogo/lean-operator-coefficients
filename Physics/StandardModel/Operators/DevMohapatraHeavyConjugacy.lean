import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyConjugacy
import Physics.StandardModel.Operators.DevMohapatraHeavyHermitian
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyConjugacy instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraHeavyConjugacy.adj => Physics.DevMohapatraHeavyConjugacy.adj,
  GUT.DevMohapatraHeavyConjugacy.adj.eq_1 => Physics.DevMohapatraHeavyConjugacy.adj.eq_1,
  GUT.DevMohapatraHeavyConjugacy.adj_add => Physics.DevMohapatraHeavyConjugacy.adj_add,
  GUT.DevMohapatraHeavyConjugacy.adj_bar_current => Physics.DevMohapatraHeavyConjugacy.adj_bar_current,
  GUT.DevMohapatraHeavyConjugacy.adj_cross => Physics.DevMohapatraHeavyConjugacy.adj_cross,
  GUT.DevMohapatraHeavyConjugacy.adj_current => Physics.DevMohapatraHeavyConjugacy.adj_current,
  GUT.DevMohapatraHeavyConjugacy.adj_generator => Physics.DevMohapatraHeavyConjugacy.adj_generator,
  GUT.DevMohapatraHeavyConjugacy.adj_involutive => Physics.DevMohapatraHeavyConjugacy.adj_involutive,
  GUT.DevMohapatraHeavyConjugacy.adj_mul => Physics.DevMohapatraHeavyConjugacy.adj_mul,
  GUT.DevMohapatraHeavyConjugacy.adj_neg => Physics.DevMohapatraHeavyConjugacy.adj_neg,
  GUT.DevMohapatraHeavyConjugacy.adj_smul => Physics.DevMohapatraHeavyConjugacy.adj_smul,
  GUT.DevMohapatraHeavyConjugacy.adj_sub => Physics.DevMohapatraHeavyConjugacy.adj_sub,
  GUT.DevMohapatraHeavyConjugacy.adj_sum => Physics.DevMohapatraHeavyConjugacy.adj_sum,
  GUT.DevMohapatraHeavyConjugacy.adj_zero => Physics.DevMohapatraHeavyConjugacy.adj_zero,
  GUT.DevMohapatraHeavyConjugacy.conjugated => Physics.DevMohapatraHeavyConjugacy.conjugated,
  GUT.DevMohapatraHeavyConjugacy.conjugated.eq_1 => Physics.DevMohapatraHeavyConjugacy.conjugated.eq_1,
  GUT.DevMohapatraHeavyConjugacy.eliminated_hermitian => Physics.DevMohapatraHeavyConjugacy.eliminated_hermitian,
  GUT.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator => Physics.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator,
  GUT.DevMohapatraHeavyConjugacy.evaluate_hc => Physics.DevMohapatraHeavyConjugacy.evaluate_hc,
  GUT.DevMohapatraHeavyConjugacy.field_bar_u => Physics.DevMohapatraHeavyConjugacy.field_bar_u,
  GUT.DevMohapatraHeavyConjugacy.field_involutive => Physics.DevMohapatraHeavyConjugacy.field_involutive,
  GUT.DevMohapatraHeavyConjugacy.include_adj => Physics.DevMohapatraHeavyConjugacy.include_adj,
  GUT.DevMohapatraHeavyConjugacy.include_injective => Physics.DevMohapatraHeavyConjugacy.include_injective,
  GUT.DevMohapatraHeavyConjugacy.residual_conjugated => Physics.DevMohapatraHeavyConjugacy.residual_conjugated,
  GUT.DevMohapatraHeavyConjugacy.solution_adjoint => Physics.DevMohapatraHeavyConjugacy.solution_adjoint,
  GUT.DevMohapatraHeavyConjugacy.solution_conjugated => Physics.DevMohapatraHeavyConjugacy.solution_conjugated,
  GUT.DevMohapatraHeavyHermitian.heavyConjugation.eq_1 => Physics.DevMohapatraHeavyHermitian.heavyConjugation.eq_1
]

assert_compatible GUT.DevMohapatraHeavyConjugacy.adj => Physics.DevMohapatraHeavyConjugacy.adj
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj.eq_1 => Physics.DevMohapatraHeavyConjugacy.adj.eq_1
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_add => Physics.DevMohapatraHeavyConjugacy.adj_add
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_bar_current => Physics.DevMohapatraHeavyConjugacy.adj_bar_current
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_cross => Physics.DevMohapatraHeavyConjugacy.adj_cross
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_current => Physics.DevMohapatraHeavyConjugacy.adj_current
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_generator => Physics.DevMohapatraHeavyConjugacy.adj_generator
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_involutive => Physics.DevMohapatraHeavyConjugacy.adj_involutive
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_mul => Physics.DevMohapatraHeavyConjugacy.adj_mul
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_neg => Physics.DevMohapatraHeavyConjugacy.adj_neg
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_smul => Physics.DevMohapatraHeavyConjugacy.adj_smul
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_sub => Physics.DevMohapatraHeavyConjugacy.adj_sub
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_sum => Physics.DevMohapatraHeavyConjugacy.adj_sum
assert_compatible GUT.DevMohapatraHeavyConjugacy.adj_zero => Physics.DevMohapatraHeavyConjugacy.adj_zero
assert_compatible GUT.DevMohapatraHeavyConjugacy.conjugated => Physics.DevMohapatraHeavyConjugacy.conjugated
assert_compatible GUT.DevMohapatraHeavyConjugacy.conjugated.eq_1 => Physics.DevMohapatraHeavyConjugacy.conjugated.eq_1
assert_compatible GUT.DevMohapatraHeavyConjugacy.eliminated_hermitian => Physics.DevMohapatraHeavyConjugacy.eliminated_hermitian
assert_compatible GUT.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator => Physics.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator
assert_compatible GUT.DevMohapatraHeavyConjugacy.evaluate_hc => Physics.DevMohapatraHeavyConjugacy.evaluate_hc
assert_compatible GUT.DevMohapatraHeavyConjugacy.field_bar_u => Physics.DevMohapatraHeavyConjugacy.field_bar_u
assert_compatible GUT.DevMohapatraHeavyConjugacy.field_involutive => Physics.DevMohapatraHeavyConjugacy.field_involutive
assert_compatible GUT.DevMohapatraHeavyConjugacy.include_adj => Physics.DevMohapatraHeavyConjugacy.include_adj
assert_compatible GUT.DevMohapatraHeavyConjugacy.include_injective => Physics.DevMohapatraHeavyConjugacy.include_injective
assert_compatible GUT.DevMohapatraHeavyConjugacy.residual_conjugated => Physics.DevMohapatraHeavyConjugacy.residual_conjugated
assert_compatible GUT.DevMohapatraHeavyConjugacy.solution_adjoint => Physics.DevMohapatraHeavyConjugacy.solution_adjoint
assert_compatible GUT.DevMohapatraHeavyConjugacy.solution_conjugated => Physics.DevMohapatraHeavyConjugacy.solution_conjugated
assert_compatible GUT.DevMohapatraHeavyHermitian.heavyConjugation.eq_1 => Physics.DevMohapatraHeavyHermitian.heavyConjugation.eq_1
