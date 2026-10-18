import Physics.StandardModel.Operators.ProhibitionInputSM
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Prohibition input imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [``GUT.ProhibitionInputSM.Forbids,
    ``GUT.ProhibitionInputSM.AllForbids,
    ``GUT.ProhibitionInputSM.facade_iff,
    ``GUT.ProhibitionInputSM.residual_iff,
    ``GUT.ProhibitionInputSM.koren,
    ``GUT.ProhibitionInputSM.bgw,
    ``GUT.ProhibitionInputSM.dgt,
    ``GUT.ProhibitionInputSM.dgt_restriction,
    ``GUT.ProhibitionInputSM.quarticity_domains,
    ``GUT.ProhibitionInputSM.llhh_forbidden_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition input: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition input: {declarations.length} strict axiom checks passed"
