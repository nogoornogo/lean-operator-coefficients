import Math.Audit.ImportOrigin
import Math.Algebra.Jets.ScalarJetQuadratic

/-! Strict scalar jet, divergence and actual quotient-consumer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Scalar jet audit imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.ScalarJetAlgebra.order,
    ``Math.ScalarJetAlgebra.weight,
    ``Math.ScalarJetAlgebra.shift,
    ``Math.ScalarJetAlgebra.weight_shift,
    ``Math.ScalarJetAlgebra.totalDerivative,
    ``Math.ScalarJetAlgebra.totalDerivative_X,
    ``Math.ScalarJetAlgebra.totalDerivative_mul,
    ``Math.ScalarJetAlgebra.totalDerivative_commute,
    ``Math.ScalarJetAlgebra.relabel,
    ``Math.ScalarJetAlgebra.totalDerivative_relabel,
    ``Math.ScalarJetAlgebra.grade,
    ``Math.ScalarJetAlgebra.totalDerivative_homogeneous,
    ``Math.ScalarJetAlgebra.totalDerivative_mem,
    ``Math.ScalarJetAlgebra.weight_relabel,
    ``Math.ScalarJetAlgebra.relabel_homogeneous,
    ``Math.ScalarJetAlgebra.exponent_bound,
    ``Math.ScalarJetAlgebra.jet_order_bound,
    ``Math.ScalarJetAlgebra.finite_monomials,
    ``Math.ScalarJetAlgebra.grade_finiteDimensional,
    ``Math.ScalarJetAlgebra.derivative,
    ``Math.ScalarJetAlgebra.relabelGrade,
    ``Math.ScalarJetAlgebra.derivative_relabelGrade,
    ``Math.ScalarJetAlgebra.multiply,
    ``Math.ScalarJetAlgebra.productLeft,
    ``Math.ScalarJetAlgebra.productRight,
    ``Math.ScalarJetAlgebra.derivative_multiply,
    ``Math.ScalarJetIBP.divergence,
    ``Math.ScalarJetIBP.divergence_single,
    ``Math.ScalarJetIBP.relations,
    ``Math.ScalarJetIBP.derivative_mem_relations,
    ``Math.ScalarJetIBP.annihilates_iff,
    ``Math.ScalarJetIBP.currentRelabel,
    ``Math.ScalarJetIBP.divergence_relabel,
    ``Math.ScalarJetIBP.action,
    ``Math.ScalarJetIBP.relations_stable,
    ``Math.ScalarJetIBP.coefficientEquiv,
    ``Math.ScalarJetIBP.coefficientEquiv_mk,
    ``Math.ScalarJetIBP.coefficientEquiv_symm,
    ``Math.ScalarJetIBP.coefficient_mem_iff,
    ``Math.ScalarJetIBP.integration_by_parts,
    ``Math.ScalarJetIBP.actions_commute,
    ``Math.ScalarJetIBP.localEquiv,
    ``Math.ScalarJetIBP.localEquiv_mk,
    ``Math.ScalarJetIBP.local_forbidden_iff,
    ``Math.ScalarJetIBP.local_nonzero_iff,
    ``Math.ScalarJetQuadratic.index_eq,
    ``Math.ScalarJetQuadratic.exponent_expansion,
    ``Math.ScalarJetQuadratic.exponent_grade_two,
    ``Math.ScalarJetQuadratic.exponent_grade_one,
    ``Math.ScalarJetQuadratic.source_reconstruct,
    ``Math.ScalarJetQuadratic.primitive_reconstruct,
    ``Math.ScalarJetQuadratic.derivative_primitive,
    ``Math.ScalarJetQuadratic.source_span,
    ``Math.ScalarJetQuadratic.relations_span,
    ``Math.ScalarJetQuadratic.reduction,
    ``Math.ScalarJetQuadratic.reduction_ker,
    ``Math.ScalarJetQuadratic.reduction_surjective,
    ``Math.ScalarJetQuadratic.quotientEquiv,
    ``Math.ScalarJetQuadratic.quotientEquiv_mk,
    ``Math.ScalarJetQuadratic.quotient_finrank,
    ``Math.ScalarJetQuadratic.first_survives,
    ``Math.ScalarJetQuadratic.ibp_identity]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Scalar jet declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Scalar jets and IBP: layer and {ds.length} strict transitive checks passed"
