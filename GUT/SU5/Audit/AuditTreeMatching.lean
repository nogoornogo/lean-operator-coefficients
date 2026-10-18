import GUT.SU5.Matching.TreeMatching
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU5.AdjointMass.background_trace,
    ``GUT.SU5.AdjointMass.background_hermitian,
    ``GUT.SU5.AdjointMass.upper_mass,
    ``GUT.SU5.AdjointMass.lower_mass,
    ``GUT.SU5.AdjointMass.massSquared_pos,
    ``GUT.SU5.AdjointMass.massSquared_ne_zero,
    ``GUT.SU5.AdjointMass.degenerate_mass,
    ``GUT.SU5.HeavyCurrents.branch_quarkEmbed,
    ``GUT.SU5.HeavyCurrents.quarkEmbed_tmul,
    ``GUT.SU5.HeavyCurrents.upCurrent_tmul,
    ``GUT.SU5.HeavyCurrents.electronCurrent_tmul,
    ``GUT.SU5.HeavyCurrents.contraction_tmul,
    ``GUT.SU5.HeavyCurrents.contraction_eq_qque,
    ``GUT.SU5.TreeMatching.eliminated_eq,
    ``GUT.SU5.TreeMatching.orderedWilson_ne_zero,
    ``GUT.SU5.TreeMatching.orderedWilson_value,
    ``GUT.SU5.TreeMatching.eliminated_probe,
    ``GUT.SU5.TreeMatching.eliminated_nonzero,
    ``GUT.SU5.TreeMatching.matchedOrdered_eq_eliminated,
    ``GUT.SU5.TreeMatching.matchedExterior_probe,
    ``GUT.SU5.TreeMatching.matchedExterior_nonzero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Tree matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Tree matching: {declarations.length} strict axiom checks passed"
