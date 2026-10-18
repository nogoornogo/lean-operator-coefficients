import GUT.SU5.SelectionRules.CopyCountProtectionConstraint
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.CopyCountProtectionConstraint.ParticipatingForbidden,
    ``GUT.SU5.CopyCountProtectionConstraint.source_le_target,
    ``GUT.SU5.CopyCountProtectionConstraint.surplus_excludes,
    ``GUT.SU5.CopyCountProtectionConstraint.parameter_retain,
    ``GUT.SU5.CopyCountProtectionConstraint.two_one_excluded,
    ``GUT.SU5.CopyCountProtectionConstraint.balancedZero,
    ``GUT.SU5.CopyCountProtectionConstraint.balancedKernel,
    ``GUT.SU5.CopyCountProtectionConstraint.balanced_counts_not_sufficient]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Copy-count constraint: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Copy-count constraint: {ds.length} strict transitive checks passed"
