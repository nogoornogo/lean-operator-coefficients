import Physics.FieldTheory.Jets.Lagrangian.RegisteredLagrangianModels
import Math.RepresentationTheory.LagrangianModel
import Physics.FieldTheory.Jets.LagrangianHelper
import Physics.FieldTheory.Jets.HiggsStandardInput
import Physics.FieldTheory.Jets.ScalarConstantCoefficients
import Physics.FieldTheory.Jets.DerivativeLiteratureScalar
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.RegisteredLagrangianModels instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.RegisteredLagrangianModels.higgs => Physics.RegisteredLagrangianModels.higgs,
  GUT.RegisteredLagrangianModels.higgs_input => Physics.RegisteredLagrangianModels.higgs_input,
  GUT.RegisteredLagrangianModels.higgs_relation => Physics.RegisteredLagrangianModels.higgs_relation,
  GUT.RegisteredLagrangianModels.quartic => Physics.RegisteredLagrangianModels.quartic,
  GUT.RegisteredLagrangianModels.quartic_cubic_value_iff => Physics.RegisteredLagrangianModels.quartic_cubic_value_iff,
  GUT.RegisteredLagrangianModels.quartic_input => Physics.RegisteredLagrangianModels.quartic_input,
  GUT.RegisteredLagrangianModels.scalar => Physics.RegisteredLagrangianModels.scalar,
  GUT.RegisteredLagrangianModels.scalar_input => Physics.RegisteredLagrangianModels.scalar_input
]

assert_compatible GUT.RegisteredLagrangianModels.higgs => Physics.RegisteredLagrangianModels.higgs
assert_compatible GUT.RegisteredLagrangianModels.higgs_input => Physics.RegisteredLagrangianModels.higgs_input
assert_compatible GUT.RegisteredLagrangianModels.higgs_relation => Physics.RegisteredLagrangianModels.higgs_relation
assert_compatible GUT.RegisteredLagrangianModels.quartic => Physics.RegisteredLagrangianModels.quartic
assert_compatible GUT.RegisteredLagrangianModels.quartic_cubic_value_iff => Physics.RegisteredLagrangianModels.quartic_cubic_value_iff
assert_compatible GUT.RegisteredLagrangianModels.quartic_input => Physics.RegisteredLagrangianModels.quartic_input
assert_compatible GUT.RegisteredLagrangianModels.scalar => Physics.RegisteredLagrangianModels.scalar
assert_compatible GUT.RegisteredLagrangianModels.scalar_input => Physics.RegisteredLagrangianModels.scalar_input
