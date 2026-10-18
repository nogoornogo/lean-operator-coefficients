import Physics.StandardModel.Operators.LiSixQuarkPrintedCompleteness
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Flavor boundary imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiSixQuarkPrintedSpan.printedSpan_eq_kernel,
    ``GUT.LiSixQuarkPrintedSpan.printed_finrank,
    ``GUT.LiSixQuarkPrintedSpan.printed_reconstruction,
    ``GUT.LiSixQuarkFlavorProjection.missing_exchange,
    ``GUT.LiSixQuarkFlavorProjection.missing_zero_iff_printed,
    ``GUT.LiSixQuarkFlavorAlternating.down_permutation,
    ``GUT.LiSixQuarkFlavorAlternating.downAlternating,
    ``GUT.LiSixQuarkFlavorAlternating.up_symmetric,
    ``GUT.LiSixQuarkFlavorAlternating.missingTensor_apply,
    ``GUT.LiSixQuarkFlavorAlternating.missingTensor_zero_iff,
    ``GUT.LiSixQuarkFlavorAlternating.missing_zero_of_down_finrank,
    ``GUT.LiSixQuarkPrintedCompleteness.physical_reconstruction,
    ``GUT.LiSixQuarkPrintedCompleteness.physical_extraction]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Flavor boundary {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li six-quark flavor boundary: {ds.length} strict axiom checks passed"
