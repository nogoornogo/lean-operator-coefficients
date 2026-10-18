import Physics.StandardModel.Operators.LLHHKernelRank
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "LLHH rank audit imports GUT {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LLHHKernelRank.coefficientEquiv,
    ``GUT.LLHHKernelRank.coordinates,
    ``GUT.LLHHKernelRank.kernelCoordinates,
    ``GUT.LLHHKernelRank.carrierBasis,
    ``GUT.LLHHKernelRank.coefficientBasis,
    ``GUT.LLHHKernelRank.reconstruct_extract,
    ``GUT.LLHHKernelRank.extract_reconstruct,
    ``GUT.LLHHKernelRank.kernel_dimension,
    ``GUT.LLHHKernelRank.carrier_dimension,
    ``GUT.LLHHKernelRank.rank,
    ``GUT.LLHHKernelRank.explicit_rank,
    ``GUT.LLHHKernelRank.rank_preserved,
    ``GUT.LLHHKernelRank.residualEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "LLHH rank audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"LLHH rank audit: layer and {ds.length} strict transitive checks passed"
