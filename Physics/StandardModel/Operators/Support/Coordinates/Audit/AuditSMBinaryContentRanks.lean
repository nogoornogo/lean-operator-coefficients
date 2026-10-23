import Physics.StandardModel.Operators.Support.Coordinates.SMBinaryContentRanks
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Binary SM content audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMBinaryContentRanks.sourceEquiv, ``Physics.SMBinaryContentRanks.source_dimension,
    ``Physics.SMBinaryContentRanks.carrier_dimension, ``Physics.SMBinaryContentRanks.charge,
    ``Physics.SMBinaryContentRanks.rank_add_nullity, ``Physics.SMBinaryContentRanks.charged_rank,
    ``Physics.SMBinaryContentRanks.odd_rank, ``Physics.SMBinaryContentRanks.reordered_source_dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Binary SM content audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Binary SM content audit: layer and {ds.length} strict transitive checks passed"
