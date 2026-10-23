import Physics.StandardModel.Operators.Weinberg.WeinbergMajorana
import Physics.StandardModel.Operators.WeinbergResidualHom
import Physics.FieldTheory.Mass.InvariantMassData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergMajorana instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergMajorana.MassCoefficients => Physics.WeinbergMajorana.MassCoefficients,
  GUT.WeinbergMajorana.evaluate => Physics.WeinbergMajorana.evaluate,
  GUT.WeinbergMajorana.evaluate.eq_1 => Physics.WeinbergMajorana.evaluate.eq_1,
  GUT.WeinbergMajorana.evaluate_nonzero_iff => Physics.WeinbergMajorana.evaluate_nonzero_iff,
  GUT.WeinbergMajorana.evaluate_zero => Physics.WeinbergMajorana.evaluate_zero,
  GUT.WeinbergMajorana.evaluationEquiv => Physics.WeinbergMajorana.evaluationEquiv,
  GUT.WeinbergMajorana.evaluationEquiv_apply => Physics.WeinbergMajorana.evaluationEquiv_apply,
  GUT.WeinbergMajorana.evaluation_formula => Physics.WeinbergMajorana.evaluation_formula,
  GUT.WeinbergMajorana.mass => Physics.WeinbergMajorana.mass,
  GUT.WeinbergMajorana.vacuum => Physics.WeinbergMajorana.vacuum,
  GUT.WeinbergMajorana.vacuum.eq_1 => Physics.WeinbergMajorana.vacuum.eq_1
]

assert_compatible GUT.WeinbergMajorana.MassCoefficients => Physics.WeinbergMajorana.MassCoefficients
assert_compatible GUT.WeinbergMajorana.evaluate => Physics.WeinbergMajorana.evaluate
assert_compatible GUT.WeinbergMajorana.evaluate.eq_1 => Physics.WeinbergMajorana.evaluate.eq_1
assert_compatible GUT.WeinbergMajorana.evaluate_nonzero_iff => Physics.WeinbergMajorana.evaluate_nonzero_iff
assert_compatible GUT.WeinbergMajorana.evaluate_zero => Physics.WeinbergMajorana.evaluate_zero
assert_compatible GUT.WeinbergMajorana.evaluationEquiv => Physics.WeinbergMajorana.evaluationEquiv
assert_compatible GUT.WeinbergMajorana.evaluationEquiv_apply => Physics.WeinbergMajorana.evaluationEquiv_apply
assert_compatible GUT.WeinbergMajorana.evaluation_formula => Physics.WeinbergMajorana.evaluation_formula
assert_compatible GUT.WeinbergMajorana.mass => Physics.WeinbergMajorana.mass
assert_compatible GUT.WeinbergMajorana.vacuum => Physics.WeinbergMajorana.vacuum
assert_compatible GUT.WeinbergMajorana.vacuum.eq_1 => Physics.WeinbergMajorana.vacuum.eq_1
