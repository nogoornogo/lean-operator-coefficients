import Physics.StandardModel.Operators.Weinberg.LLHHKernelRank
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "LLHH rank audit imports GUT {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LLHHKernelRank.coefficientEquiv,
    ``Physics.LLHHKernelRank.coordinates,
    ``Physics.LLHHKernelRank.kernelCoordinates,
    ``Physics.LLHHKernelRank.carrierBasis,
    ``Physics.LLHHKernelRank.coefficientBasis,
    ``Physics.LLHHKernelRank.reconstruct_extract,
    ``Physics.LLHHKernelRank.extract_reconstruct,
    ``Physics.LLHHKernelRank.kernel_dimension,
    ``Physics.LLHHKernelRank.carrier_dimension,
    ``Physics.LLHHKernelRank.rank,
    ``Physics.LLHHKernelRank.explicit_rank,
    ``Physics.LLHHKernelRank.rank_preserved,
    ``Physics.LLHHKernelRank.residualEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "LLHH rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"LLHH rank audit: layer and {ds.length} strict transitive checks passed"
