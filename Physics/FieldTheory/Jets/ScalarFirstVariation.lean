import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarFirstVariation
import Math.Algebra.JetFirstVariation
import Physics.FieldTheory.Jets.PolynomialScalarEOM
import Physics.FieldTheory.Jets.FormalYangMills
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarFirstVariation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarFirstVariation.current => Physics.ScalarFirstVariation.current,
  GUT.ScalarFirstVariation.current.eq_1 => Physics.ScalarFirstVariation.current.eq_1,
  GUT.ScalarFirstVariation.delta => Physics.ScalarFirstVariation.delta,
  GUT.ScalarFirstVariation.delta_field => Physics.ScalarFirstVariation.delta_field,
  GUT.ScalarFirstVariation.delta_first => Physics.ScalarFirstVariation.delta_first,
  GUT.ScalarFirstVariation.eulerEquation => Physics.ScalarFirstVariation.eulerEquation,
  GUT.ScalarFirstVariation.euler_ideal_eq => Physics.ScalarFirstVariation.euler_ideal_eq,
  GUT.ScalarFirstVariation.first_variation => Physics.ScalarFirstVariation.first_variation,
  GUT.ScalarFirstVariation.first_variation_mod_ibp => Physics.ScalarFirstVariation.first_variation_mod_ibp,
  GUT.ScalarFirstVariation.first_variation_onShell => Physics.ScalarFirstVariation.first_variation_onShell,
  GUT.ScalarFirstVariation.lagrangian => Physics.ScalarFirstVariation.lagrangian,
  GUT.ScalarFirstVariation.substitution_first => Physics.ScalarFirstVariation.substitution_first
]

assert_compatible GUT.ScalarFirstVariation.current => Physics.ScalarFirstVariation.current
assert_compatible GUT.ScalarFirstVariation.current.eq_1 => Physics.ScalarFirstVariation.current.eq_1
assert_compatible GUT.ScalarFirstVariation.delta => Physics.ScalarFirstVariation.delta
assert_compatible GUT.ScalarFirstVariation.delta_field => Physics.ScalarFirstVariation.delta_field
assert_compatible GUT.ScalarFirstVariation.delta_first => Physics.ScalarFirstVariation.delta_first
assert_compatible GUT.ScalarFirstVariation.eulerEquation => Physics.ScalarFirstVariation.eulerEquation
assert_compatible GUT.ScalarFirstVariation.euler_ideal_eq => Physics.ScalarFirstVariation.euler_ideal_eq
assert_compatible GUT.ScalarFirstVariation.first_variation => Physics.ScalarFirstVariation.first_variation
assert_compatible GUT.ScalarFirstVariation.first_variation_mod_ibp => Physics.ScalarFirstVariation.first_variation_mod_ibp
assert_compatible GUT.ScalarFirstVariation.first_variation_onShell => Physics.ScalarFirstVariation.first_variation_onShell
assert_compatible GUT.ScalarFirstVariation.lagrangian => Physics.ScalarFirstVariation.lagrangian
assert_compatible GUT.ScalarFirstVariation.substitution_first => Physics.ScalarFirstVariation.substitution_first
