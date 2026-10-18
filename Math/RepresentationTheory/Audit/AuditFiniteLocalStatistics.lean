import Math.RepresentationTheory.FiniteLocalIsotypicCompleteness
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.FiniteLocalStatistics.matrix_one,
    ``Math.FiniteLocalStatistics.matrix_mul,
    ``Math.FiniteLocalStatistics.matrix_agrees,
    ``Math.FiniteLocalStatistics.inputMap_single,
    ``Math.FiniteLocalStatistics.statistics,
    ``Math.FiniteLocalStatistics.commutes,
    ``Math.FiniteLocalIsotypicCompleteness.compatible,
    ``Math.FiniteLocalIsotypicCompleteness.equiv,
    ``Math.CharacterRelationStability.action_relation,
    ``Math.CharacterRelationStability.stable,
    ``Math.FiniteLocalIsotypicCompleteness.statistics_stable,
    ``Math.FiniteLocalIsotypicCompleteness.characterQuotientEquiv,
    ``Math.FiniteLocalIsotypicCompleteness.extraction,
    ``Math.FiniteLocalIsotypicCompleteness.reconstruction,
    ``Math.FiniteLocalIsotypicCompleteness.quotientCommutes,
    ``Math.FiniteLocalIsotypicCompleteness.characterIsotypicEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite local statistics: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite local statistics: {declarations.length} strict transitive checks passed"
