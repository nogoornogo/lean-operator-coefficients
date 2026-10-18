import Physics.StandardModel.Operators.LiSixQuarkProbeDecomposition
import Physics.StandardModel.Operators.LiSixQuarkExchangeBlocks
import Physics.StandardModel.Operators.LiSixQuarkPairBlock
import Physics.StandardModel.Operators.LiSixQuarkBlockCoordinates
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
  let ds := [``GUT.LiSixQuarkExtension.withoutExtra_mem_kernel,
    ``GUT.LiSixQuarkExtension.reconstruct_withoutExtra,
    ``GUT.LiSixQuarkExtension.decomposition_unique,
    ``GUT.LiSixQuarkExtension.probeDecomposition,
    ``GUT.LiSixQuarkExtension.probe_kernel_finrank,
    ``GUT.LiSixQuarkExtension.extra_color_action,
    ``GUT.LiSixQuarkExtension.extra_spin_action,
    ``GUT.LiSixQuarkExtension.transform_outer,
    ``GUT.LiSixQuarkExtension.extra_transform,
    ``GUT.LiSixQuarkExchangeBlocks.exchange_involutive,
    ``GUT.LiSixQuarkExchangeBlocks.reconstruct,
    ``GUT.LiSixQuarkExchangeBlocks.blocks_unique,
    ``GUT.LiSixQuarkExchangeBlocks.kernel_le_iff_blocks,
    ``GUT.LiSixQuarkPairBlock.encode_zero_iff,
    ``GUT.LiSixQuarkPairBlock.reconstruction,
    ``GUT.LiSixQuarkPairBlock.probe_encode,
    ``GUT.LiSixQuarkPairBlock.kernel_reconstruction,
    ``GUT.LiSixQuarkBlockCoordinates.colorEquiv,
    ``GUT.LiSixQuarkBlockCoordinates.spinEquiv,
    ``GUT.LiSixQuarkBlockCoordinates.localBlocks]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Probe decomposition: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li probe decomposition: {ds.length} strict transitive checks passed"
