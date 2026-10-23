import Physics.StandardModel.Operators.Dipole.DipolePolynomialControls
import Physics.StandardModel.Operators.DipolePolynomialInputs
import Physics.StandardModel.Operators.DipoleMediatorControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipolePolynomialControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipolePolynomialControls.generation => Physics.DipolePolynomialControls.generation,
  GUT.DipolePolynomialControls.generation.eq_1 => Physics.DipolePolynomialControls.generation.eq_1,
  GUT.DipolePolynomialControls.not_isolates => Physics.DipolePolynomialControls.not_isolates,
  GUT.DipolePolynomialControls.polynomials => Physics.DipolePolynomialControls.polynomials,
  GUT.DipolePolynomialControls.polynomials.eq_1 => Physics.DipolePolynomialControls.polynomials.eq_1,
  GUT.DipolePolynomialControls.realized => Physics.DipolePolynomialControls.realized,
  GUT.DipolePolynomialControls.same_monomial_cancels => Physics.DipolePolynomialControls.same_monomial_cancels,
  GUT.DipolePolynomialControls.selected => Physics.DipolePolynomialControls.selected,
  GUT.DipolePolynomialControls.weights => Physics.DipolePolynomialControls.weights,
  GUT.DipolePolynomialControls.weights.eq_1 => Physics.DipolePolynomialControls.weights.eq_1
]

assert_compatible GUT.DipolePolynomialControls.generation => Physics.DipolePolynomialControls.generation
assert_compatible GUT.DipolePolynomialControls.generation.eq_1 => Physics.DipolePolynomialControls.generation.eq_1
assert_compatible GUT.DipolePolynomialControls.not_isolates => Physics.DipolePolynomialControls.not_isolates
assert_compatible GUT.DipolePolynomialControls.polynomials => Physics.DipolePolynomialControls.polynomials
assert_compatible GUT.DipolePolynomialControls.polynomials.eq_1 => Physics.DipolePolynomialControls.polynomials.eq_1
assert_compatible GUT.DipolePolynomialControls.realized => Physics.DipolePolynomialControls.realized
assert_compatible GUT.DipolePolynomialControls.same_monomial_cancels => Physics.DipolePolynomialControls.same_monomial_cancels
assert_compatible GUT.DipolePolynomialControls.selected => Physics.DipolePolynomialControls.selected
assert_compatible GUT.DipolePolynomialControls.weights => Physics.DipolePolynomialControls.weights
assert_compatible GUT.DipolePolynomialControls.weights.eq_1 => Physics.DipolePolynomialControls.weights.eq_1
