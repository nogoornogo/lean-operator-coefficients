import Math.RepresentationTheory.AdmittedCyclicProhibition
import Math.RepresentationTheory.Multiplicity.CopySumEquivalence
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Math.AdmittedCyclicProhibition.forbidden_iff,
    ``Math.AdmittedCyclicProhibition.all_forbidden_iff,
    ``Math.CopySumEquivalence.copiesAdd,
    ``Math.CopySumEquivalence.copiesProd,
    ``Math.CopySumEquivalence.assoc]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Math converse boundaries: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Math converse boundaries: {ds.length} strict transitive checks passed"
