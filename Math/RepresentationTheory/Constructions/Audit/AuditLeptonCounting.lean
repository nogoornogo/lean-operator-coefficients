import Math.RepresentationTheory.SU2.SL2SpanContinuity
import Math.RepresentationTheory.Exterior.ExteriorContinuity
import Math.RepresentationTheory.SU2.SU2SignedWeights
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Lepton counting audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.SL2SpanContinuity.continuous_orbit,
    ``Math.SL2SpanContinuity.jointlyContinuous,
    ``Math.ExteriorContinuity.continuous_orbit,
    ``Math.ExteriorContinuity.representation_continuous,
    ``Math.SU2CoefficientExtraction.allowed_iff_finrank_ne_zero,
    ``Math.SU2CoefficientExtraction.finrank,
    ``Math.SU2CoefficientExtraction.haarProb_prod,
    ``Math.SU2CoefficientExtraction.pair_finrank,
    ``Math.SU2SignedWeights.signed_pair,
    ``Math.SU2SignedWeights.expansion,
    ``Math.SU2SignedWeights.coefficient_finrank]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Lepton counting: layer and {ds.length} strict transitive checks passed"
