import Physics.StandardModel.Operators.BaryonOne.Inputs.LiFourFamilyCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Four-family imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LiFourFamilyCertificate.duql_eq,
    ``Physics.LiFourFamilyCertificate.duue_eq, ``Physics.LiFourFamilyCertificate.qqql_eq,
    ``Physics.LiFourFamilyCertificate.qque_eq, ``Physics.LiFourFamilyCertificate.candidate_eq,
    ``Physics.LiFourFamilyCertificate.qque_literal,
    ``Physics.LiFourFamilyCertificate.extract_candidate,
    ``Physics.LiFourFamilyCertificate.candidate_extract]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-family {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li four-family: {ds.length} strict axiom checks passed"
