import Math.RepresentationTheory.Relations.BiaffineStatisticalOrbits
import Math.RepresentationTheory.SU2.SL2StatisticalSpan
import Math.RepresentationTheory.Relations.StatisticalSourceRestriction
import Math.RepresentationTheory.SU2.SL2PairCompactComparison
import Math.RepresentationTheory.Coefficients.SeparatedInvariantCoefficients
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Mixed chirality math audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.PolynomialRealForm.eval_coordinates,
    ``Math.PolynomialRealForm.zero_of_conjugate_diagonal,
    ``Math.PairedPolynomialInvariants.fixed_iff, ``Math.PairedPolynomialInvariants.fixed_iff_action,
    ``Math.BiaffineStatisticalOrbits.add, ``Math.BiaffineStatisticalOrbits.smul,
    ``Math.BiaffineStatisticalOrbits.multilinear_affine, ``Math.BiaffineStatisticalOrbits.raw_polynomial,
    ``Math.BiaffineStatisticalOrbits.descend, ``Math.BiaffineStatisticalOrbits.tensor_fixed,
    ``Math.SL2StatisticalSpan.single, ``Math.SL2StatisticalSpan.pi, ``Math.SL2StatisticalSpan.source,
    ``Math.StatisticalSourceRestriction.source, ``Math.StatisticalSourceRestriction.tensor,
    ``Math.SL2PairCompactComparison.fixed_iff, ``Math.SeparatedInvariantCoefficients.Space,
    ``Math.SeparatedInvariantCoefficients.fixed_iff, ``Math.SeparatedInvariantCoefficients.equiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed chirality math audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed chirality math audit: layer and {ds.length} strict transitive checks passed"
