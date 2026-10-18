import Physics.StandardModel.Operators.SlotSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Slot support imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StandardModelSlotSupport.slotsSupported_of_chargesSupported,
    ``GUT.StandardModelSlotSupport.qque_slotsSupported_iff,
    ``GUT.StandardModelSlotSupport.slotwise_prohibition_implies_legacy,
    ``GUT.StandardModelSlotSupport.not_slotwise_prohibition_of_qque,
    ``GUT.StandardModelSlotSupport.legacy_prohibition_of_no_lepton]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Slot support: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Slot support: layer and {declarations.length} strict axiom checks passed"
