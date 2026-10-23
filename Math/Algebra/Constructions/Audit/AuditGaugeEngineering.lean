import Math.Audit.ImportOrigin
import Math.Algebra.Constructions.FormalGaugeTransformation
import Math.Algebra.Jets.MatrixTraceIBP
import Math.Algebra.Constructions.FormalGaugeExample
import Math.Algebra.Jets.JetEngineeringDegree
import Math.Algebra.Constructions.ScalarEngineeringTwo

/-! Explicit public declaration inventory with strict transitive axiom/layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.FormalConnection.ordinary_one,
    ``Math.FormalConnection.derivative_inverse,
    ``Math.FormalConnection.gauge,
    ``Math.FormalConnection.gauge_covariant,
    ``Math.FormalConnection.gauge_curvature,
    ``Math.FormalConnection.gauge_one,
    ``Math.FormalConnection.gauge_composition,
    ``Math.FormalConnection.signedEquation,
    ``Math.FormalConnection.gauge_equation,
    ``Math.MatrixTraceIBP.ordinary,
    ``Math.MatrixTraceIBP.trace_bracket,
    ``Math.MatrixTraceIBP.trace_ordinary,
    ``Math.MatrixTraceIBP.trace_covariant,
    ``Math.MatrixTraceIBP.trace_ibp,
    ``Math.MatrixTraceIBP.trace_conjugate,
    ``Math.MatrixTraceIBP.trace_ibp_integrated,
    ``Math.FormalGaugeExample.Poly,
    ``Math.FormalGaugeExample.Mat,
    ``Math.FormalGaugeExample.field,
    ``Math.FormalGaugeExample.ordinary,
    ``Math.FormalGaugeExample.unit,
    ``Math.FormalGaugeExample.unit_nonconstant,
    ``Math.FormalGaugeExample.transformed_zero,
    ``Math.FormalGaugeExample.transformed_flat,
    ``Math.JetEngineering.weight,
    ``Math.JetEngineering.grade,
    ``Math.JetEngineering.weight_shift,
    ``Math.JetEngineering.finite_monomials,
    ``Math.JetEngineering.grade_finite,
    ``Math.JetEngineering.derivative_homogeneous,
    ``Math.JetEngineering.product_homogeneous,
    ``Math.JetEngineering.matrix_product_mem,
    ``Math.JetEngineering.eomImage,
    ``Math.JetEngineering.ibpImage,
    ``Math.JetEngineering.eomImage_finite,
    ``Math.JetEngineering.ibpImage_finite,
    ``Math.ScalarEngineeringTwo.J,
    ``Math.ScalarEngineeringTwo.zeroIndex,
    ``Math.ScalarEngineeringTwo.firstIndex,
    ``Math.ScalarEngineeringTwo.weight_zero,
    ``Math.ScalarEngineeringTwo.index_weight_one,
    ``Math.ScalarEngineeringTwo.exponent_weight_one,
    ``Math.ScalarEngineeringTwo.index_weight_two,
    ``Math.ScalarEngineeringTwo.exponent_weight_two,
    ``Math.ScalarEngineeringTwo.Source,
    ``Math.ScalarEngineeringTwo.square,
    ``Math.ScalarEngineeringTwo.first,
    ``Math.ScalarEngineeringTwo.source_reconstruct]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Formal gauge, trace and engineering degree: {ds.length} strict transitive checks passed"
