import Physics.StandardModel.Operators.LiFourFamilyCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Four-family imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiFourFamilyCertificate.duql_eq,
    ``GUT.LiFourFamilyCertificate.duue_eq, ``GUT.LiFourFamilyCertificate.qqql_eq,
    ``GUT.LiFourFamilyCertificate.qque_eq, ``GUT.LiFourFamilyCertificate.candidate_eq,
    ``GUT.LiFourFamilyCertificate.qque_literal,
    ``GUT.LiFourFamilyCertificate.extract_candidate,
    ``GUT.LiFourFamilyCertificate.candidate_extract]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-family {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li four-family: {ds.length} strict axiom checks passed"
