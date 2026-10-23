import Physics.StandardModel.Operators.Support.Coordinates.SMConstantContentRanks
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Numerical rank audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMParityKernelRank.raw_minus,
    ``Physics.SMParityKernelRank.source_minus, ``Physics.SMParityKernelRank.action_minus,
    ``Physics.SMParityKernelRank.forbidden, ``Physics.SMParityKernelRank.full_rank,
    ``Physics.SMConstantContentRanks.source_dimension,
    ``Physics.SMConstantContentRanks.carrier_dimension,
    ``Physics.SMConstantContentRanks.charge,
    ``Physics.SMConstantContentRanks.charged_rank,
    ``Physics.SMConstantContentRanks.above_capacity_rank,
    ``Physics.SMConstantContentRanks.evaluate_sound]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Numerical rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Numerical rank audit: layer and {ds.length} strict transitive checks passed"
