import Math.RepresentationTheory.Exterior.CompactGenerationOccupations
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "compact Math audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.CompactGenerationOccupations.triples,
    ``Math.CompactGenerationOccupations.mem_triples,
    ``Math.CompactGenerationOccupations.contiguous,
    ``Math.CompactGenerationOccupations.contiguous_counts,
    ``Math.CompactGenerationOccupations.counts_cast,
    ``Math.CompactGenerationOccupations.attainable_iff,
    ``Math.CompactGenerationOccupations.fromTriple,
    ``Math.CompactGenerationOccupations.Index,
    ``Math.CompactGenerationOccupations.toOccupation,
    ``Math.CompactGenerationOccupations.fromOccupation,
    ``Math.CompactGenerationOccupations.equiv,
    ``Math.CompactGenerationOccupations.fintype,
    ``Math.CompactGenerationOccupations.choiceFintype]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "compact support audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"compact support: {ds.length} strict transitive checks passed"
