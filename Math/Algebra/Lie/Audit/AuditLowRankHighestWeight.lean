import Math.Algebra.Lie.StandardSl2
import Math.Algebra.Lie.Sl3HighestWeightExistence
import Lean.Util.CollectAxioms

/-! Persistent transitive axiom audit for the relocated low-rank Lie results.
Declaration namespaces are preserved for compatibility. -/

#print axioms Math.Sl2String.exists_highestWeight_and_dimension
#print axioms Math.StandardSl2.isSl2Triple
#print axioms Math.StandardSl2.toLieSubalgebra_eq_top
#print axioms Math.StandardSl3.lieSpan_simpleGenerators_eq_top
#print axioms Math.StandardSl3.upperBorel_derivedSeries_three_eq_bot
#print axioms Math.Sl3HighestWeight.exists_highestWeightVector
#print axioms Math.Sl3HighestWeight.finrank_eq_one_or_three_or_six

run_cmd do
  let declarations := [
    ``Math.Sl2String.exists_highestWeight_and_dimension,
    ``Math.StandardSl2.isSl2Triple,
    ``Math.StandardSl2.toLieSubalgebra_eq_top,
    ``Math.StandardSl3.lieSpan_simpleGenerators_eq_top,
    ``Math.StandardSl3.upperBorel_derivedSeries_three_eq_bot,
    ``Math.Sl3HighestWeight.exists_highestWeightVector,
    ``Math.Sl3HighestWeight.finrank_eq_one_or_three_or_six]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Low-rank Lie audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Low-rank Lie: {declarations.length} strict transitive checks passed"
