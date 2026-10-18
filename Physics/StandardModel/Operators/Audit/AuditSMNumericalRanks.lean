import Physics.StandardModel.Operators.SMConstantContentRanks
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Numerical rank audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMParityKernelRank.raw_minus,
    ``GUT.SMParityKernelRank.source_minus, ``GUT.SMParityKernelRank.action_minus,
    ``GUT.SMParityKernelRank.forbidden, ``GUT.SMParityKernelRank.full_rank,
    ``GUT.SMConstantContentRanks.source_dimension,
    ``GUT.SMConstantContentRanks.carrier_dimension,
    ``GUT.SMConstantContentRanks.charge,
    ``GUT.SMConstantContentRanks.charged_rank,
    ``GUT.SMConstantContentRanks.above_capacity_rank,
    ``GUT.SMConstantContentRanks.evaluate_sound]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Numerical rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Numerical rank audit: layer and {ds.length} strict transitive checks passed"
