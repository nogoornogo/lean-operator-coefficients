import Math.RepresentationTheory.Constructions.ScalarEigencharacter
import Math.RepresentationTheory.Decomposition.FirstSummandEmbedding
import Math.RepresentationTheory.Decomposition.RepresentationConjugation
open Lean in
run_cmd do
  let ds := [``Math.ScalarEigencharacter.character, ``Math.ScalarEigencharacter.character_apply,
    ``Math.ScalarEigencharacter.onEmbedding, ``Math.ScalarEigencharacter.onEmbedding_apply,
    ``Math.FirstSummandEmbedding.embedding, ``Math.FirstSummandEmbedding.linear,
    ``Math.FirstSummandEmbedding.linear_apply, ``Math.FirstSummandEmbedding.scaled_action,
    ``Math.FirstSummandEmbedding.action, ``Math.FirstSummandEmbedding.decomposed,
    ``Math.RepresentationConjugation.pullback_apply]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Scalar/block mathematics {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Scalar/block mathematics: {ds.length} strict transitive checks passed"
