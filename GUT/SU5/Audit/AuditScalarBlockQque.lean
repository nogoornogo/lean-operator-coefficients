import GUT.SU5.SelectionRules.ScalarBlockMassExtension
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Strict transitive checks for the actual SU5 scalar/block and mass
extension endpoints; no SU6 import is admitted. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "SU5 scalar/block imports SU6: {mod}"
  let declarations := [
    ``GUT.SU5.ScalarBlockQque.coords,
    ``GUT.SU5.ScalarBlockQque.fiveBlocks,
    ``GUT.SU5.ScalarBlockQque.blocks,
    ``GUT.SU5.ScalarBlockQque.fundamental_action,
    ``GUT.SU5.ScalarBlockQque.pair_action,
    ``GUT.SU5.ScalarBlockQque.blocksLinear,
    ``GUT.SU5.ScalarBlockQque.branch_action,
    ``GUT.SU5.ScalarBlockQque.diagonal_commutes,
    ``GUT.SU5.ScalarBlockQque.uvRho,
    ``GUT.SU5.ScalarBlockQque.uvInner,
    ``GUT.SU5.ScalarBlockQque.externalLinear,
    ``GUT.SU5.ScalarBlockQque.physical_commutes_sm,
    ``GUT.SU5.ScalarBlockQque.joint,
    ``GUT.SU5.ScalarBlockQque.embedding,
    ``GUT.SU5.ScalarBlockQque.embedding_injective,
    ``GUT.SU5.ScalarBlockQque.embedding_action,
    ``GUT.SU5.ScalarBlockQque.quarkLinear,
    ``GUT.SU5.ScalarBlockQque.upLinear,
    ``GUT.SU5.ScalarBlockQque.electronLinear,
    ``GUT.SU5.ScalarBlockQque.quark_injective,
    ``GUT.SU5.ScalarBlockQque.quark_action,
    ``GUT.SU5.ScalarBlockQque.quark_gauge_action,
    ``GUT.SU5.ScalarBlockQque.up_injective,
    ``GUT.SU5.ScalarBlockQque.up_action,
    ``GUT.SU5.ScalarBlockQque.up_gauge_action,
    ``GUT.SU5.ScalarBlockQque.electron_injective,
    ``GUT.SU5.ScalarBlockQque.electron_action,
    ``GUT.SU5.ScalarBlockQque.electron_gauge_action,
    ``GUT.SU5.ScalarBlockQque.quarkCharacter,
    ``GUT.SU5.ScalarBlockQque.upCharacter,
    ``GUT.SU5.ScalarBlockQque.electronCharacter,
    ``GUT.SU5.ScalarBlockQque.charges,
    ``GUT.SU5.ScalarBlockQque.neutral,
    ``GUT.SU5.ScalarBlockQque.quarkCoords,
    ``GUT.SU5.ScalarBlockQque.upCoords,
    ``GUT.SU5.ScalarBlockQque.electronCoords,
    ``GUT.SU5.ScalarBlockQque.quark_coords,
    ``GUT.SU5.ScalarBlockQque.up_coords,
    ``GUT.SU5.ScalarBlockQque.electron_coords,
    ``GUT.SU5.ScalarBlockQque.quarkRho,
    ``GUT.SU5.ScalarBlockQque.upLeftRho,
    ``GUT.SU5.ScalarBlockQque.electronLeftRho,
    ``GUT.SU5.ScalarBlockQque.quark_residual_action,
    ``GUT.SU5.ScalarBlockQque.up_residual_action,
    ``GUT.SU5.ScalarBlockQque.electron_residual_action,
    ``GUT.SU5.ScalarBlockQque.quark_gauge_restriction,
    ``GUT.SU5.ScalarBlockQque.up_gauge_restriction,
    ``GUT.SU5.ScalarBlockQque.electron_gauge_restriction,
    ``GUT.SU5.ScalarBlockQque.quark_joint_action,
    ``GUT.SU5.ScalarBlockQque.up_joint_action,
    ``GUT.SU5.ScalarBlockQque.electron_joint_action,
    ``GUT.SU5.ScalarBlockQque.quarkEq,
    ``GUT.SU5.ScalarBlockQque.upEq,
    ``GUT.SU5.ScalarBlockQque.electronEq,
    ``GUT.SU5.ScalarBlockQque.exists_actual_exterior,
    ``GUT.SU5.ScalarBlockQque.trivialInput,
    ``GUT.SU5.ScalarBlockQque.zeroMass,
    ``GUT.SU5.ScalarBlockQque.zeroMass_light,
    ``GUT.SU5.ScalarBlockQque.LightMass.jointMass,
    ``GUT.SU5.ScalarBlockQque.LightMass.joint_radical,
    ``GUT.SU5.ScalarBlockQque.radical_stable,
    ``GUT.SU5.ScalarBlockQque.quarkSpace_light,
    ``GUT.SU5.ScalarBlockQque.upSpace_light,
    ``GUT.SU5.ScalarBlockQque.electronSpace_light,
    ``GUT.SU5.ScalarBlockQque.zeroLightMass,
    ``GUT.SU5.ScalarBlockQque.exists_light_exterior,
    ``GUT.SU5.ScalarBlockMassExtension.heavyRho,
    ``GUT.SU5.ScalarBlockMassExtension.mass,
    ``GUT.SU5.ScalarBlockMassExtension.mass_apply,
    ``GUT.SU5.ScalarBlockMassExtension.retained_light,
    ``GUT.SU5.ScalarBlockMassExtension.radical_finrank,
    ``GUT.SU5.ScalarBlockMassExtension.mass_nonzero,
    ``GUT.SU5.ScalarBlockMassExtension.exists_retained_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU5 scalar/block: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU5 scalar/block: {declarations.length} strict transitive axiom checks passed"
