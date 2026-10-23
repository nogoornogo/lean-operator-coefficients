import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkProbeDecomposition
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExchangeBlocks
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPairBlock
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkBlockCoordinates
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! This pilot must stay independent of the dense Li certificate. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Probe decomposition imports model layer {mod}; original {SourceLayout.originalModule mod}"
    if [`Physics.StandardModel.Operators.LiSixQuarkFiniteData,
        `Physics.StandardModel.Operators.LiSixQuarkOrbitData,
        `Physics.StandardModel.Operators.LiSixQuarkCertificate,
        `Physics.StandardModel.Operators.LiSixQuarkLocalBasis,
        `Physics.StandardModel.Operators.LiSixQuarkPrintedSpan].contains mod then
      throwError "Probe decomposition imports dense certificate consumer {mod}"
  let ds := [``Physics.LiSixQuarkExtension.withoutExtra_mem_kernel,
    ``Physics.LiSixQuarkExtension.reconstruct_withoutExtra,
    ``Physics.LiSixQuarkExtension.decomposition_unique,
    ``Physics.LiSixQuarkExtension.probeDecomposition,
    ``Physics.LiSixQuarkExtension.probe_kernel_finrank,
    ``Physics.LiSixQuarkExtension.extra_color_action,
    ``Physics.LiSixQuarkExtension.extra_spin_action,
    ``Physics.LiSixQuarkExtension.transform_outer,
    ``Physics.LiSixQuarkExtension.extra_transform,
    ``Physics.LiSixQuarkExchangeBlocks.exchange_involutive,
    ``Physics.LiSixQuarkExchangeBlocks.reconstruct,
    ``Physics.LiSixQuarkExchangeBlocks.blocks_unique,
    ``Physics.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks,
    ``Physics.LiSixQuarkPairBlock.encode_zero_iff,
    ``Physics.LiSixQuarkPairBlock.reconstruction,
    ``Physics.LiSixQuarkPairBlock.probe_encode,
    ``Physics.LiSixQuarkPairBlock.kernel_reconstruction,
    ``Physics.LiSixQuarkBlockCoordinates.colorEquiv,
    ``Physics.LiSixQuarkBlockCoordinates.spinEquiv,
    ``Physics.LiSixQuarkBlockCoordinates.localBlocks]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Probe decomposition: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li probe decomposition: {ds.length} strict transitive checks passed"
