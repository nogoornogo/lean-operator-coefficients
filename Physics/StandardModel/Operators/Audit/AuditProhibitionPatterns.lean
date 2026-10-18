import Physics.StandardModel.Operators.ProhibitionPatterns
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Prohibition patterns imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.ProhibitionPatterns.BLTarget,
    ``GUT.ProhibitionPatterns.target,
    ``GUT.ProhibitionPatterns.specification,
    ``GUT.ProhibitionPatterns.request,
    ``GUT.ProhibitionPatterns.ForbidsChosen,
    ``GUT.ProhibitionPatterns.chosen_iff,
    ``GUT.ProhibitionPatterns.triple_iff,
    ``GUT.ProhibitionPatterns.empty_chosen,
    ``GUT.ProhibitionPatterns.JointForbids,
    ``GUT.ProhibitionPatterns.joint_iff,
    ``GUT.ProhibitionPatterns.koren_chosen,
    ``GUT.ProhibitionPatterns.baryonTargets,
    ``GUT.ProhibitionPatterns.bgw_baryon,
    ``GUT.ProhibitionPatterns.dgt_uv_baryon,
    ``GUT.ProhibitionPatterns.dgt_joint]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition patterns: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition patterns: {ds.length} strict transitive checks passed"
