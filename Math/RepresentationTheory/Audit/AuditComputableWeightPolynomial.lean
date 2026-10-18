import Math.RepresentationTheory.ComputableWeightPolynomial
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "computable weight audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ComputableWeightPolynomial.coefficient, ``Math.ComputableWeightPolynomial.shift,
    ``Math.ComputableWeightPolynomial.multiply, ``Math.ComputableWeightPolynomial.exterior,
    ``Math.ComputableWeightPolynomial.product, ``Math.ComputableWeightPolynomial.presentation_apply,
    ``Math.ComputableWeightPolynomial.presentation_evaluate, ``Math.ComputableWeightPolynomial.evaluate_append,
    ``Math.ComputableWeightPolynomial.evaluate_shift, ``Math.ComputableWeightPolynomial.evaluate_multiply,
    ``Math.ComputableWeightPolynomial.exterior_evaluate, ``Math.ComputableWeightPolynomial.exterior_above,
    ``Math.ComputableWeightPolynomial.evaluate_product, ``Math.ComputableWeightPolynomial.exterior_length,
    ``Math.ComputableWeightPolynomial.exterior_ofFn_evaluate]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "computable weight audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"computable weight audit: layer and {ds.length} strict transitive checks passed"
