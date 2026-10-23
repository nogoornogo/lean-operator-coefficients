import Math.LinearAlgebra.Constructions.SplitEvaluation
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``SplitEvaluation.equiv, ``SplitEvaluation.surjective,
    ``SplitEvaluation.equivWithKernel, ``SplitEvaluation.equivWithKernel_symm_apply,
    ``SplitEvaluation.finrank]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Split evaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Split evaluation: {declarations.length} strict axiom checks passed"
