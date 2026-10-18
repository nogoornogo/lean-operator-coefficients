import Math.RepresentationTheory.AffineStatisticalSampling
import Math.RepresentationTheory.PartialInvariantKernel
import Math.LieGroups.SpecialUnitary.AffinePairBoundary
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Statistical finite kernel imports application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.AffineStatisticalSampling.zero,
    ``Math.AffineStatisticalSampling.add,
    ``Math.AffineStatisticalSampling.smul,
    ``Math.AffineStatisticalSampling.constant,
    ``Math.AffineStatisticalSampling.multilinear_affine,
    ``Math.AffineStatisticalSampling.raw_polynomial,
    ``Math.AffineStatisticalSampling.descend,
    ``Math.AffineStatisticalSampling.tensor_fixed,
    ``Math.AffineStatisticalSampling.statistical_source,
    ``Math.AffineStatisticalSampling.samples_injective,
    ``Math.AffineStatisticalSampling.family_invariant,
    ``Math.PartialInvariantKernel.Space,
    ``Math.PartialInvariantKernel.equiv,
    ``Math.PartialInvariantKernel.allowed_iff,
    ``Math.AffinePairBoundary.normalized_pair,
    ``Math.AffinePairBoundary.row_norm,
    ``Math.AffinePairBoundary.actual_row]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Statistical finite kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Statistical finite kernel: layer and {ds.length} strict transitive axiom checks passed"
