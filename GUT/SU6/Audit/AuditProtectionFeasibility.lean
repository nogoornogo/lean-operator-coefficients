import GUT.SU6.SelectionRules.Models.ProtectionFeasibilityControls
import Lean.Util.CollectAxioms

/-! Audit every declaration in the new namespace, including generated helpers. -/
run_cmd do
  let env ← Lean.getEnv
  let ds := env.constants.toList.filterMap fun (d, _) =>
    if d.toString.startsWith "GUT.SU6ProtectionFeasibility." ||
        (d.toString.splitOn ".GUT.SU6ProtectionFeasibility.").length > 1 then
      some d
    else none
  unless ds.contains ``GUT.SU6ProtectionFeasibility.target_forces_yukawa_neutral &&
      ds.contains ``GUT.SU6ProtectionFeasibility.no_target_of_light_forbidden &&
      ds.contains ``GUT.SU6ProtectionFeasibility.Controls.lepton_parity_ir_success_uv_failure &&
      ds.contains ``GUT.SU6ProtectionFeasibility.Controls.unequal_s3_screen do
    throwError "SU(6) protection feasibility: required consumers missing"
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU(6) protection feasibility: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU(6) protection feasibility: {ds.length} strict transitive checks passed"
