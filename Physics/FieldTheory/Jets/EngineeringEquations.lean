import Physics.FieldTheory.Jets.Scalar.Inputs.EngineeringEquations
import Math.Algebra.JetEngineeringDegree
import Physics.FieldTheory.Jets.PolynomialScalarEOM
import Physics.FieldTheory.Jets.FormalYangMills
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.EngineeringEquations instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.EngineeringEquations.connection_degree => Physics.EngineeringEquations.connection_degree,
  GUT.EngineeringEquations.covariant_degree => Physics.EngineeringEquations.covariant_degree,
  GUT.EngineeringEquations.curvature_degree => Physics.EngineeringEquations.curvature_degree,
  GUT.EngineeringEquations.equation_degree => Physics.EngineeringEquations.equation_degree,
  GUT.EngineeringEquations.scalar_equation => Physics.EngineeringEquations.scalar_equation,
  GUT.EngineeringEquations.scalar_field => Physics.EngineeringEquations.scalar_field,
  GUT.FormalYangMills.connection.eq_1 => Physics.FormalYangMills.connection.eq_1
]

assert_compatible GUT.EngineeringEquations.connection_degree => Physics.EngineeringEquations.connection_degree
assert_compatible GUT.EngineeringEquations.covariant_degree => Physics.EngineeringEquations.covariant_degree
assert_compatible GUT.EngineeringEquations.curvature_degree => Physics.EngineeringEquations.curvature_degree
assert_compatible GUT.EngineeringEquations.equation_degree => Physics.EngineeringEquations.equation_degree
assert_compatible GUT.EngineeringEquations.scalar_equation => Physics.EngineeringEquations.scalar_equation
assert_compatible GUT.EngineeringEquations.scalar_field => Physics.EngineeringEquations.scalar_field
assert_compatible GUT.FormalYangMills.connection.eq_1 => Physics.FormalYangMills.connection.eq_1
