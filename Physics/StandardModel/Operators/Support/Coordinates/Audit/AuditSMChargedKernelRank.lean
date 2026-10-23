import Physics.StandardModel.Operators.Support.Coordinates.SMChargedKernelRank
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM rank audit imports GUT {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMChargedKernelRank.local_charge,
    ``Physics.SMChargedKernelRank.full_rank,
    ``Physics.SMChargedKernelRank.dimension_zero_above_cutoff,
    ``Physics.SMChargedKernelRank.rank_zero_above_cutoff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM rank audit: layer and {ds.length} strict transitive checks passed"
