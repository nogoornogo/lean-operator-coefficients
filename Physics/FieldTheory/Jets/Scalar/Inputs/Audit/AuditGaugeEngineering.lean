import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Gauge.YangMillsGaugeTrace
import Physics.FieldTheory.Jets.Scalar.Inputs.EngineeringEquations
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarEngineeringClassification

/-! Explicit public declaration inventory with strict transitive axiom/layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.FormalYangMills.transformedConnection,
    ``Physics.FormalYangMills.local_curvature,
    ``Physics.FormalYangMills.local_equation,
    ``Physics.FormalYangMills.local_equation_mem,
    ``Physics.FormalYangMills.local_equation_zero,
    ``Physics.FormalYangMills.trace_local_curvature_square,
    ``Physics.FormalYangMills.trace_ibp,
    ``Physics.FormalYangMills.trace_ibp_onShell,
    ``Physics.EngineeringEquations.scalar_field,
    ``Physics.EngineeringEquations.scalar_equation,
    ``Physics.EngineeringEquations.connection_degree,
    ``Physics.EngineeringEquations.curvature_degree,
    ``Physics.EngineeringEquations.covariant_degree,
    ``Physics.EngineeringEquations.equation_degree,
    ``Physics.ScalarEngineeringClassification.polynomialEvaluation,
    ``Physics.ScalarEngineeringClassification.evaluation_shift,
    ``Physics.ScalarEngineeringClassification.evaluation_derivative,
    ``Physics.ScalarEngineeringClassification.evaluation_seed,
    ``Physics.ScalarEngineeringClassification.cubicIdeal,
    ``Physics.ScalarEngineeringClassification.eom_evaluation_mem,
    ``Physics.ScalarEngineeringClassification.coefficient,
    ``Physics.ScalarEngineeringClassification.coefficient_eom,
    ``Physics.ScalarEngineeringClassification.coefficient_derivative,
    ``Physics.ScalarEngineeringClassification.combined_le_kernel,
    ``Physics.ScalarEngineeringClassification.quotientCoefficient,
    ``Physics.ScalarEngineeringClassification.coefficient_square,
    ``Physics.ScalarEngineeringClassification.square_survives,
    ``Physics.ScalarEngineeringClassification.Source,
    ``Physics.ScalarEngineeringClassification.image,
    ``Physics.ScalarEngineeringClassification.sourceProjection,
    ``Physics.ScalarEngineeringClassification.sourceProjection_surjective,
    ``Physics.ScalarEngineeringClassification.generator,
    ``Physics.ScalarEngineeringClassification.first_zero,
    ``Physics.ScalarEngineeringClassification.reconstruction,
    ``Physics.ScalarEngineeringClassification.generator_nonzero,
    ``Physics.ScalarEngineeringClassification.coordinate,
    ``Physics.ScalarEngineeringClassification.coordinate_generator,
    ``Physics.ScalarEngineeringClassification.equivalence,
    ``Physics.ScalarEngineeringClassification.basis,
    ``Physics.ScalarEngineeringClassification.dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Yang-Mills gauge trace and complete scalar degree two: {ds.length} strict transitive checks passed"
