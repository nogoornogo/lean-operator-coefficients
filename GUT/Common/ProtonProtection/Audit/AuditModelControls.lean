import GUT.Common.ProtonProtection.ModelControls
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.ProtonProtectionModelControls.baryon_families_nonzero,
    ``GUT.ProtonProtectionModelControls.baryon_selection,
    ``GUT.ProtonProtectionModelControls.baryon_qque_all_flavors,
    ``GUT.ProtonProtectionModelControls.light_parity_families_nonzero,
    ``GUT.ProtonProtectionModelControls.light_parity_selection,
    ``GUT.ProtonProtectionModelControls.gauge_only_qque_allowed,
    ``GUT.ProtonProtectionModelControls.equal_scalars_of_common_embeddings]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"ProtonProtectionModelControls: {declarations.length} strict transitive axiom checks passed"
