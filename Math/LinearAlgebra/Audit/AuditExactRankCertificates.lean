import Math.LinearAlgebra.ExactRankCertificateExamples
import Math.RepresentationTheory.PatternMultiplicityEquiv
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Exact rank audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExactRankCertificate.Certificate.ofActions, ``Math.ExactRankCertificate.rank_eq, ``Math.ExactRankCertificate.map,
    ``Math.ExactRankCertificate.mapped_rank, ``Math.ExactRankCertificate.mapped_nullity,
    ``Math.ExactRankCertificate.example_complex_rank,
    ``Math.ExactRankExamples.rank0, ``Math.ExactRankExamples.rank1,
    ``Math.ExactRankExamples.rank2, ``Math.ExactRankExamples.rank3,
    ``Math.ExactRankExamples.rank4,
    ``Math.PatternMultiplicityEquiv.source_eq, ``Math.PatternMultiplicityEquiv.equiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exact rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact rank audit: layer and {ds.length} strict transitive checks passed"
