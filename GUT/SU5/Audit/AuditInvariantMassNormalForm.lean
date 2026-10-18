import GUT.SU5.SelectionRules.InvariantMassNormalForm
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "Unexpected original SU6 dependency: {mod}"
  let declarations := [
    ``GUT.SU5.InvariantMassNormalForm.HasHypercharge,
    ``GUT.SU5.InvariantMassNormalForm.hypercharge_dual,
    ``GUT.SU5.InvariantMassNormalForm.quark_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.upRight_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.downRight_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.lepton_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.electronRight_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.trivial_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.upLeft_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.downLeft_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.electronLeft_hypercharge,
    ``GUT.SU5.InvariantMassNormalForm.bounded_weights_separated,
    ``GUT.SU5.InvariantMassNormalForm.no_pair_of_weights,
    ``GUT.SU5.InvariantMassNormalForm.blocks_ten_ten,
    ``GUT.SU5.InvariantMassNormalForm.blocks_ten_bar,
    ``GUT.SU5.InvariantMassNormalForm.blocks_bar_ten,
    ``GUT.SU5.InvariantMassNormalForm.blocks_bar_bar,
    ``GUT.SU5.InvariantMassNormalForm.blocks_dual_ten_dual_ten,
    ``GUT.SU5.InvariantMassNormalForm.dualTenBlocksEquiv,
    ``GUT.SU5.InvariantMassNormalForm.ten_ten,
    ``GUT.SU5.InvariantMassNormalForm.ten_bar,
    ``GUT.SU5.InvariantMassNormalForm.bar_ten,
    ``GUT.SU5.InvariantMassNormalForm.bar_bar,
    ``GUT.SU5.InvariantMassNormalForm.dual_ten_dual_ten,
    ``GUT.SU5.InvariantMassNormalForm.upI,
    ``GUT.SU5.InvariantMassNormalForm.quarkI,
    ``GUT.SU5.InvariantMassNormalForm.electronI,
    ``GUT.SU5.InvariantMassNormalForm.upP,
    ``GUT.SU5.InvariantMassNormalForm.quarkP,
    ``GUT.SU5.InvariantMassNormalForm.electronP,
    ``GUT.SU5.InvariantMassNormalForm.blocks_endomorphism,
    ``GUT.SU5.InvariantMassNormalForm.ten_endomorphism,
    ``GUT.SU5.InvariantMassNormalForm.bar_dual_ten,
    ``GUT.SU5.InvariantMassNormalForm.bar_to_ten_zero,
    ``GUT.SU5.InvariantMassNormalForm.sourceSM,
    ``GUT.SU5.InvariantMassNormalForm.targetSM,
    ``GUT.SU5.InvariantMassNormalForm.source_no_pairings,
    ``GUT.SU5.InvariantMassNormalForm.target_dual_no_pairings,
    ``GUT.SU5.InvariantMassNormalForm.source_restriction,
    ``GUT.SU5.InvariantMassNormalForm.target_restriction,
    ``GUT.SU5.InvariantMassNormalForm.source_joint_no_pairings,
    ``GUT.SU5.InvariantMassNormalForm.target_joint_dual_no_pairings,
    ``GUT.SU5.InvariantMassNormalForm.normal_form,
    ``GUT.SU5.InvariantMassNormalForm.restrictMassMap,
    ``GUT.SU5.InvariantMassNormalForm.entry,
    ``GUT.SU5.InvariantMassNormalForm.rows,
    ``GUT.SU5.InvariantMassNormalForm.rows_spec,
    ``GUT.SU5.InvariantMassNormalForm.matrices,
    ``GUT.SU5.InvariantMassNormalForm.reconstructed_map,
    ``GUT.SU5.InvariantMassNormalForm.massMap_eq,
    ``GUT.SU5.InvariantMassNormalForm.matrix_normal_form,
    ``GUT.SU5.InvariantMassNormalForm.arbitrary_mass_light_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.SU5.InvariantMassNormalForm: {declarations.length} strict transitive axiom checks passed"
