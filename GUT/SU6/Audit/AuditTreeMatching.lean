import GUT.SU6.Matching.TreeMatching
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU6.ExteriorCurrents.restrict_include,
    ``GUT.SU6.ExteriorCurrents.cut_action,
    ``GUT.SU6.ExteriorCurrents.project_embed,
    ``GUT.SU6.ExteriorCurrents.branch_embed,
    ``GUT.SU6.ExteriorCurrents.quark_branch,
    ``GUT.SU6.ExteriorCurrents.quark_covariant,
    ``GUT.SU6.ExteriorCurrents.coreAction_eq,
    ``GUT.SU6.ExteriorCurrents.upCurrent_core,
    ``GUT.SU6.ExteriorCurrents.electronCurrent_core,
    ``GUT.SU6.ExteriorCurrents.upCurrent_extra,
    ``GUT.SU6.ExteriorCurrents.electronCurrent_extra,
    ``GUT.SU6.ExteriorCurrents.actual_action,
    ``GUT.SU6.AdjointMass.background_trace,
    ``GUT.SU6.AdjointMass.background_hermitian,
    ``GUT.SU6.AdjointMass.upper_mass,
    ``GUT.SU6.AdjointMass.lower_mass,
    ``GUT.SU6.AdjointMass.massSquared_pos,
    ``GUT.SU6.AdjointMass.massSquared_ne_zero,
    ``GUT.SU6.AdjointMass.covers_broken_entries,
    ``GUT.SU6.AdjointMass.equal_weight_entry_zero,
    ``GUT.SU6.TreeMatching.retainedLeft_eq,
    ``GUT.SU6.TreeMatching.retainedRight_eq,
    ``GUT.SU6.TreeMatching.extraLeft_zero,
    ``GUT.SU6.TreeMatching.extraRight_zero,
    ``GUT.SU6.TreeMatching.leftCurrent_eq,
    ``GUT.SU6.TreeMatching.rightCurrent_eq,
    ``GUT.SU6.TreeMatching.coefficient_eq,
    ``GUT.SU6.TreeMatching.invariant,
    ``GUT.SU6.TreeMatching.generated_eq,
    ``GUT.SU6.TreeMatching.generated_nonzero,
    ``GUT.SU6.TreeMatching.full_action_eq]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU6 tree matching: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU6 tree matching: {declarations.length} strict axiom checks passed"
