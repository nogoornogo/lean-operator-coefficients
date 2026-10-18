import Physics.StandardModel.Operators.SMBinaryContentRanks
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Binary SM content audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMBinaryContentRanks.sourceEquiv, ``GUT.SMBinaryContentRanks.source_dimension,
    ``GUT.SMBinaryContentRanks.carrier_dimension, ``GUT.SMBinaryContentRanks.charge,
    ``GUT.SMBinaryContentRanks.rank_add_nullity, ``GUT.SMBinaryContentRanks.charged_rank,
    ``GUT.SMBinaryContentRanks.odd_rank, ``GUT.SMBinaryContentRanks.reordered_source_dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Binary SM content audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Binary SM content audit: layer and {ds.length} strict transitive checks passed"
