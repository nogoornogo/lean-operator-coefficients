import Math.Audit.ImportOrigin
import Math.Algebra.Jets.DifferentialEquationIdeal
import Math.RepresentationTheory.Jets.NonlinearJetIBP
import Math.Algebra.Jets.NonlinearJetLinearRecovery
import Math.Algebra.Constructions.FormalConnection
import Math.Algebra.Jets.MatrixJetConnection

/-! Explicit public declaration inventory, strict transitive axiom and layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.DifferentialEquation.word,
    ``Math.DifferentialEquation.ideal,
    ``Math.DifferentialEquation.descendant_mem,
    ``Math.DifferentialEquation.seed_mem,
    ``Math.DifferentialEquation.stable,
    ``Math.DifferentialEquation.minimal,
    ``Math.DifferentialEquation.ideal_le_solution_kernel,
    ``Math.DifferentialEquation.one_not_mem,
    ``Math.DifferentialEquation.Shell,
    ``Math.DifferentialEquation.projection,
    ``Math.DifferentialEquation.projection_surjective,
    ``Math.DifferentialEquation.projection_kernel,
    ``Math.DifferentialEquation.projection_eq_zero,
    ``Math.DifferentialEquation.derivative,
    ``Math.DifferentialEquation.derivative_projection,
    ``Math.DifferentialEquation.derivative_commute,
    ``Math.DifferentialEquation.relations,
    ``Math.DifferentialEquation.linear_kernel,
    ``Math.DifferentialEquation.image,
    ``Math.DifferentialEquation.imageProjection,
    ``Math.DifferentialEquation.imageProjection_surjective,
    ``Math.DifferentialEquation.image_finite,
    ``Math.DifferentialEquation.map_stable,
    ``Math.ScalarJetAlgebra.zeroEvaluation,
    ``Math.ScalarJetAlgebra.zeroEvaluation_X,
    ``Math.ScalarJetAlgebra.zeroEvaluation_derivative,
    ``Math.ScalarJetAlgebra.constantEvaluation,
    ``Math.ScalarJetAlgebra.constantEvaluation_X_zero,
    ``Math.ScalarJetAlgebra.constantEvaluation_shift,
    ``Math.ScalarJetAlgebra.constantEvaluation_derivative,
    ``Math.DifferentialEquation.transport,
    ``Math.DifferentialEquation.transport_projection,
    ``Math.DifferentialEquation.divergence,
    ``Math.DifferentialEquation.divergence_single,
    ``Math.DifferentialEquation.ibp,
    ``Math.DifferentialEquation.derivative_mem_ibp,
    ``Math.DifferentialEquation.shell_ibp_map,
    ``Math.DifferentialEquation.combined,
    ``Math.DifferentialEquation.combined_comap,
    ``Math.DifferentialEquation.combinedProjection,
    ``Math.DifferentialEquation.combinedProjection_kernel,
    ``Math.DifferentialEquation.combinedProjection_surjective,
    ``Math.DifferentialEquation.sourceEquiv,
    ``Math.DifferentialEquation.sourceEquiv_mk,
    ``Math.DifferentialEquation.coefficientEquiv,
    ``Math.DifferentialEquation.integrated,
    ``Math.DifferentialEquation.integrated_derivative,
    ``Math.DifferentialEquation.integrated_equation,
    ``Math.DifferentialEquation.integration_by_parts,
    ``Math.DifferentialEquation.ibp_map_stable,
    ``Math.DifferentialEquation.combined_map_stable,
    ``Math.DifferentialEquation.integratedTransport,
    ``Math.DifferentialEquation.scalar_linear_recovery,
    ``Math.FormalConnection.Ordinary,
    ``Math.FormalConnection.bracket,
    ``Math.FormalConnection.covariant,
    ``Math.FormalConnection.covariant_apply,
    ``Math.FormalConnection.curvature,
    ``Math.FormalConnection.covariant_mul,
    ``Math.FormalConnection.curvature_skew,
    ``Math.FormalConnection.curvature_self,
    ``Math.FormalConnection.covariant_commutator,
    ``Math.FormalConnection.bianchi,
    ``Math.FormalConnection.conjugate_covariant,
    ``Math.FormalConnection.conjugate_curvature,
    ``Math.FormalConnection.matrixDerivative,
    ``Math.FormalConnection.matrixDerivative_apply,
    ``Math.FormalConnection.matrixOrdinary,
    ``Math.FormalConnection.zeroOrdinary,
    ``Math.FormalConnection.noncommutingControl,
    ``Math.FormalConnection.curvature_control,
    ``Math.FormalConnection.curvature_control_nonzero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Nonlinear equations and formal connections: {ds.length} strict transitive checks passed"
