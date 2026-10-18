import GUT.Common.ProtonProtection.LRModelAdmissionControls
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.LRModelAdmissionControls.both_unit_identity,
    ``GUT.LRModelAdmissionControls.both_unit_kernel,
    ``GUT.LRModelAdmissionControls.both_zero,
    ``GUT.LRModelAdmissionControls.both_zero_kernel,
    ``GUT.LRModelAdmissionControls.unit_full_lr_equivariant,
    ``GUT.LRModelAdmissionControls.positive_selection,
    ``GUT.LRModelAdmissionControls.unit_fails_selection,
    ``GUT.LRModelAdmissionControls.selection_not_universal,
    ``GUT.BLResidualRestriction.vev_stabilizer,
    ``GUT.BLResidualRestriction.actual_field_restriction,
    ``GUT.LRLightHiggs.kernel_of_coordinates,
    ``GUT.LRLightHiggs.lightRepresentationEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "BL/LR model admission: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"BL/LR model admission: {ds.length} strict transitive checks passed"
