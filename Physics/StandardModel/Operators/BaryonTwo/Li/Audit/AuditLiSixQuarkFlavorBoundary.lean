import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPrintedCompleteness
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Flavor boundary imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LiSixQuarkPrintedSpan.printedSpan_eq_kernel,
    ``Physics.LiSixQuarkPrintedSpan.printed_finrank,
    ``Physics.LiSixQuarkPrintedSpan.printed_reconstruction,
    ``Physics.LiSixQuarkFlavorProjection.missing_exchange,
    ``Physics.LiSixQuarkFlavorProjection.missing_zero_iff_printed,
    ``Physics.LiSixQuarkFlavorAlternating.down_permutation,
    ``Physics.LiSixQuarkFlavorAlternating.downAlternating,
    ``Physics.LiSixQuarkFlavorAlternating.up_symmetric,
    ``Physics.LiSixQuarkFlavorAlternating.missingTensor_apply,
    ``Physics.LiSixQuarkFlavorAlternating.missingTensor_zero_iff,
    ``Physics.LiSixQuarkFlavorAlternating.missing_zero_of_down_finrank,
    ``Physics.LiSixQuarkPrintedCompleteness.physical_reconstruction,
    ``Physics.LiSixQuarkPrintedCompleteness.physical_extraction]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Flavor boundary {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li six-quark flavor boundary: {ds.length} strict axiom checks passed"
