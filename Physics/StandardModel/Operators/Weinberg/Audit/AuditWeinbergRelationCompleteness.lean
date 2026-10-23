import Physics.StandardModel.Operators.Weinberg.WeinbergRelationCompleteness
import Lean.Util.CollectAxioms

/-! Physical consumer of the general input-relation quotient. -/
run_cmd do
  let declarations := [
    ``Physics.WeinbergRelationCompleteness.normalized,
    ``Physics.WeinbergRelationCompleteness.complete,
    ``Physics.WeinbergRelationCompleteness.generatorEquiv,
    ``Physics.WeinbergRelationCompleteness.equiv,
    ``Physics.WeinbergRelationCompleteness.extraction,
    ``Physics.WeinbergRelationCompleteness.symmetricHomEquiv,
    ``Physics.WeinbergRelationCompleteness.symmetricHomEquiv_agrees,
    ``Physics.WeinbergRelationCompleteness.modelEquiv,
    ``Physics.WeinbergRelationCompleteness.modelEquiv_agrees]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg relation completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg relation completeness: {declarations.length} strict transitive checks passed"
