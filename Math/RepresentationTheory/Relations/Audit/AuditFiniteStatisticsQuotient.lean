import Math.RepresentationTheory.Relations.FiniteStatisticsQuotient
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.FiniteStatisticsQuotient.average_formula,
    ``Math.FiniteStatisticsQuotient.average_right,
    ``Math.FiniteStatisticsQuotient.average_commutes,
    ``Math.FiniteStatisticsQuotient.invariants_stable,
    ``Math.FiniteStatisticsQuotient.average_vanish,
    ``Math.FiniteStatisticsQuotient.average_sub_mem,
    ``Math.FiniteStatisticsQuotient.equiv,
    ``Math.FiniteStatisticsQuotient.equiv_mk,
    ``Math.FiniteStatisticsQuotient.equiv_symm,
    ``Math.FiniteStatisticsQuotient.twisted,
    ``Math.FiniteStatisticsQuotient.twisted_commutes,
    ``Math.FiniteStatisticsQuotient.characterEquiv,
    ``Math.FiniteStatisticsQuotient.mem_twisted]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite statistics: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite statistics: {declarations.length} strict transitive checks passed"
