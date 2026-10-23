import Physics.StandardModel.Operators.Support.Coordinates.SMIteratedContent
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Iterated SM content audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMIteratedContent.labelEquiv, ``Physics.SMIteratedContent.fieldEquiv,
    ``Physics.SMIteratedContent.degree_eq, ``Physics.SMIteratedContent.sourceEquiv,
    ``Physics.SMIteratedContent.source_dimension, ``Physics.SMIteratedContent.carrier_dimension,
    ``Physics.SMIteratedContent.source_character, ``Physics.SMIteratedContent.withSpectator,
    ``Physics.SMIteratedContent.coefficientEquiv, ``Physics.SMIteratedContent.rank_add_nullity,
    ``Physics.SMIteratedContent.charged_rank, ``Physics.SMIteratedContent.odd_rank]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Iterated SM content audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Iterated SM content audit: layer and {ds.length} strict transitive checks passed"
