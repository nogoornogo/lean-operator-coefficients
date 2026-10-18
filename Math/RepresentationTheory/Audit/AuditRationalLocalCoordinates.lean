import Math.RepresentationTheory.GaussianCompactTests
import Math.LinearAlgebra.ExactPowerCoordinates
import Math.LinearAlgebra.GramNullityPolynomial
import Math.RepresentationTheory.ConstantExteriorAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Exact local coordinate audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.RationalCircleTests.trace_sample,
    ``Math.RationalCircleTests.not_integral_trace,
    ``Math.RationalCircleTests.pow_ne_one,
    ``Math.RationalCircleTests.zpow_ne_one,
    ``Math.RationalCircleTests.invariant,
    ``Math.RationalCircleTests.conjugate_invariant,
    ``Math.RationalCompactTests.weak_exhaustive,
    ``Math.RationalCompactTests.color_exhaustive,
    ``Math.GaussianRational.injective,
    ``Math.GaussianRational.embed_star,
    ``Math.GaussianRational.gramPolynomial_map,
    ``Math.GaussianRational.natTrailingDegree_map,
    ``Math.GramNullityPolynomial.nullity,
    ``Math.ExactPowerCoordinates.exterior_coordinate,
    ``Math.ExactPowerCoordinates.symmetric_map,
    ``Math.ExactPowerCoordinates.symmetricFormula_eq,
    ``Math.GaussianCompactTests.torus_embed,
    ``Math.GaussianCompactTests.mix_embed,
    ``Math.GaussianCompactTests.weak_embed,
    ``Math.GaussianCompactTests.color_embed,
    ``Math.ConstantExteriorAction.forward_action]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact local coordinates: layer and {ds.length} strict transitive checks passed"
