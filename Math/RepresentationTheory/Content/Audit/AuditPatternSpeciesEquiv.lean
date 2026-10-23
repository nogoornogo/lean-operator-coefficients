import Math.RepresentationTheory.Exterior.IndexedExteriorContent
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Species dictionary audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.PatternSpeciesEquiv.total_at, ``Math.PatternSpeciesEquiv.total_single,
    ``Math.PatternSpeciesEquiv.raw_pure, ``Math.PatternSpeciesEquiv.forward_pure,
    ``Math.PatternSpeciesEquiv.source_ext, ``Math.PatternSpeciesEquiv.inclusion_forward,
    ``Math.PatternSpeciesEquiv.forward_injective, ``Math.PatternSpeciesEquiv.forward_surjective,
    ``Math.PatternSpeciesEquiv.equiv, ``Math.IndexedExteriorContent.headTail,
    ``Math.IndexedExteriorContent.labels, ``Math.IndexedExteriorContent.fieldEquiv,
    ``Math.IndexedExteriorContent.dictionaryEquiv, ``Math.IndexedExteriorContent.decomposition,
    ``Math.IndexedExteriorContent.degree_eq, ``Math.IndexedExteriorContent.pattern_append,
    ``Math.IndexedExteriorContent.pattern_counts, ``Math.IndexedExteriorContent.degree_of_counts,
    ``Math.IndexedExteriorContent.wordDecomposition, ``Math.IndexedExteriorContent.finiteLeaves,
    ``Math.IndexedExteriorContent.dimensionFormula_eq, ``Math.IndexedExteriorContent.word_dimension,
    ``Math.IndexedExteriorContent.characterFormula_eq, ``Math.IndexedExteriorContent.word_character,
    ``Math.IndexedExteriorContent.wordWithSpectator, ``Math.IndexedExteriorContent.wordCoefficientEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Species dictionary audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Species dictionary audit: layer and {ds.length} strict transitive checks passed"
