import GUT.SU6.Yukawa.InvisibleCoupling
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.SU6CouplingEvaluation.evaluation,
    ``GUT.SU6CouplingEvaluation.coordinates, ``GUT.SU6CouplingEvaluation.coordinates_coupling,
    ``GUT.SU6CouplingEvaluation.sectionMap, ``GUT.SU6CouplingEvaluation.coordinates_section,
    ``GUT.SU6CouplingEvaluation.evaluation_eq_iff, ``GUT.SU6CouplingEvaluation.kernel_eq,
    ``GUT.SU6CouplingEvaluation.split, ``GUT.SU6CouplingEvaluation.coordinates_surjective,
    ``GUT.SU6CouplingEvaluation.quotientEquiv, ``GUT.SU6CouplingEvaluation.quotient_finrank,
    ``GUT.SU6CouplingEvaluation.dimension_split,
    ``GUT.SU6CouplingEvaluation.dimension_twenty_two_iff,
    ``GUT.SU6CouplingEvaluation.evaluation_section, ``GUT.SU6CouplingEvaluation.reconstruction,
    ``GUT.SU6CouplingEvaluation.unique_decomposition,
    ``GUT.SU6InvisibleCoupling.invisible, ``GUT.SU6InvisibleCoupling.evaluation_zero,
    ``GUT.SU6InvisibleCoupling.invisible_probe, ``GUT.SU6InvisibleCoupling.nonzero,
    ``GUT.SU6InvisibleCoupling.nonzero_kernel]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Coupling evaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Coupling evaluation: {declarations.length} strict axiom checks passed"
