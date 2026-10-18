import Physics.StandardModel.Operators.SMIteratedContent
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Iterated SM content audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMIteratedContent.labelEquiv, ``GUT.SMIteratedContent.fieldEquiv,
    ``GUT.SMIteratedContent.degree_eq, ``GUT.SMIteratedContent.sourceEquiv,
    ``GUT.SMIteratedContent.source_dimension, ``GUT.SMIteratedContent.carrier_dimension,
    ``GUT.SMIteratedContent.source_character, ``GUT.SMIteratedContent.withSpectator,
    ``GUT.SMIteratedContent.coefficientEquiv, ``GUT.SMIteratedContent.rank_add_nullity,
    ``GUT.SMIteratedContent.charged_rank, ``GUT.SMIteratedContent.odd_rank]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Iterated SM content audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Iterated SM content audit: layer and {ds.length} strict transitive checks passed"
