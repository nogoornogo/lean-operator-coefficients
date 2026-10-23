import Physics.StandardModel.Operators.Selection.ProhibitionPatterns
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Prohibition patterns imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.ProhibitionPatterns.BLTarget,
    ``Physics.ProhibitionPatterns.target,
    ``Physics.ProhibitionPatterns.specification,
    ``Physics.ProhibitionPatterns.request,
    ``Physics.ProhibitionPatterns.ForbidsChosen,
    ``Physics.ProhibitionPatterns.chosen_iff,
    ``Physics.ProhibitionPatterns.triple_iff,
    ``Physics.ProhibitionPatterns.empty_chosen,
    ``Physics.ProhibitionPatterns.JointForbids,
    ``Physics.ProhibitionPatterns.joint_iff,
    ``Physics.ProhibitionPatterns.koren_chosen,
    ``Physics.ProhibitionPatterns.baryonTargets,
    ``Physics.ProhibitionPatterns.bgw_baryon,
    ``Physics.ProhibitionPatterns.dgt_uv_baryon,
    ``Physics.ProhibitionPatterns.dgt_joint]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition patterns: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition patterns: {ds.length} strict transitive checks passed"
