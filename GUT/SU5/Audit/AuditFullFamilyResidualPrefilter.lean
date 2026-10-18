import GUT.SU5.SelectionRules.FullFamilyResidualPrefilter
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.FullFamilyResidualPrefilter.protected_constraints,
    ``GUT.SU5.FullFamilyResidualPrefilter.joint_reject,
    ``GUT.SU5.FullFamilyResidualPrefilter.neutral_reject,
    ``GUT.SU5.FullFamilyResidualPrefilter.uniformTriplet,
    ``GUT.SU5.FullFamilyResidualPrefilter.uniformSM_gauge,
    ``GUT.SU5.FullFamilyResidualPrefilter.uniformSM_reject]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Full-family residual prefilter: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Full-family residual prefilter: {ds.length} strict transitive checks passed"
