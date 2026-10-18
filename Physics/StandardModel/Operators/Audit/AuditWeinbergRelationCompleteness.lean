import Physics.StandardModel.Operators.WeinbergRelationCompleteness
import Lean.Util.CollectAxioms

/-! Physical consumer of the general input-relation quotient. -/
run_cmd do
  let declarations := [
    ``GUT.WeinbergRelationCompleteness.normalized,
    ``GUT.WeinbergRelationCompleteness.complete,
    ``GUT.WeinbergRelationCompleteness.generatorEquiv,
    ``GUT.WeinbergRelationCompleteness.equiv,
    ``GUT.WeinbergRelationCompleteness.extraction,
    ``GUT.WeinbergRelationCompleteness.symmetricHomEquiv,
    ``GUT.WeinbergRelationCompleteness.symmetricHomEquiv_agrees,
    ``GUT.WeinbergRelationCompleteness.modelEquiv,
    ``GUT.WeinbergRelationCompleteness.modelEquiv_agrees]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg relation completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg relation completeness: {declarations.length} strict transitive checks passed"
