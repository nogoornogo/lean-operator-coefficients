import Math.RepresentationTheory.SU2.WeightStringExtraction
import Math.RepresentationTheory.Exterior.GroupedExteriorPolynomial
import Math.RepresentationTheory.Coefficients.BoundedExteriorCoefficient
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "sparse weight audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.BoundedExteriorCoefficient.mem_bounds,
    ``Math.BoundedExteriorCoefficient.coefficient_zero,
    ``Math.BoundedExteriorCoefficient.lower_slots,
    ``Math.BoundedExteriorCoefficient.upper_slots,
    ``Math.BoundedExteriorCoefficient.impossible_zero,
    ``Math.BoundedExteriorCoefficient.coefficient_step,
    ``Math.BoundedExteriorCoefficient.compute_eq,
    ``Math.BoundedExteriorCoefficient.compute_cons,
    ``Math.GroupedExteriorPolynomial.evaluate_scaledShift,
    ``Math.GroupedExteriorPolynomial.tripleStep_evaluation,
    ``Math.GroupedExteriorPolynomial.rows_evaluation,
    ``Math.SparseWeightPolynomial.evaluate_mergeFuel,
    ``Math.SparseWeightPolynomial.evaluate_merge,
    ``Math.SparseWeightPolynomial.evaluate_multiply,
    ``Math.SparseWeightPolynomial.evaluate_multiplyFast,
    ``Math.SparseWeightPolynomial.evaluate_normalize,
    ``Math.SparseWeightPolynomial.evaluate_product,
    ``Math.SparseWeightPolynomial.rows_length,
    ``Math.SparseWeightPolynomial.exterior_evaluation,
    ``Math.SparseWeightPolynomial.exteriorFast_evaluation,
    ``Math.SparseWeightPolynomial.formal_coefficient,
    ``Math.SparseWeightPolynomial.multiplyFast_one_left,
    ``Math.SparseWeightPolynomial.multiplyFast_one_right,
    ``Math.SparseWeightPolynomial.rows_zero,
    ``Math.WeightStringExtraction.coefficient_append,
    ``Math.WeightStringExtraction.coefficient_scaledShift,
    ``Math.WeightStringExtraction.coefficient_multiply,
    ``Math.WeightStringExtraction.telescope,
    ``Math.WeightStringExtraction.difference_string,
    ``Math.WeightStringExtraction.extractAt_append,
    ``Math.WeightStringExtraction.extractAt_difference,
    ``Math.WeightStringExtraction.constantTerm_string]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "sparse weight audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"sparse weight audit: layer and {ds.length} strict transitive checks passed"
