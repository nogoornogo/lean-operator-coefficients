import Math.LinearAlgebra.Constructions.NeutralKernelGraph
import Math.LinearAlgebra.Constructions.LightLineNormalization
import Math.LinearAlgebra.Constructions.TwoSourceQuadraticElimination
import Math.RepresentationTheory.Content.MixedSinglePatternEvaluation
import Math.RepresentationTheory.Constructions.MixedSingleBosonEvaluation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Symbolic coefficient bridge imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.NeutralKernelGraph.graph_kernel,
    ``Math.NeutralKernelGraph.kernel_iff,
    ``Math.NeutralKernelGraph.graph_injective,
    ``Math.NeutralKernelGraph.restrict_apply,
    ``Math.NeutralKernelGraph.restrict_nonzero_iff,
    ``Math.NeutralKernelGraph.restrict_zero_iff_on_kernel,
    ``Math.NeutralKernelGraph.restrict_change_coordinates,
    ``Math.LightLineNormalization.scale_ne_zero,
    ``Math.LightLineNormalization.unit_norm,
    ``Math.LightLineNormalization.unit_mem_kernel,
    ``Math.LightLineNormalization.normalized_value,
    ``Math.LightLineNormalization.normalized_value_ne_zero_iff,
    ``Math.LightLineNormalization.comp_equiv_ne_zero_iff,
    ``Math.TwoSourceQuadraticElimination.shifted_action,
    ``Math.TwoSourceQuadraticElimination.on_shell,
    ``Math.TwoSourceQuadraticElimination.stationary_variation,
    ``Math.MixedSinglePatternEvaluation.assembly_value,
    ``Math.MixedSingleBosonEvaluation.substitute_apply,
    ``Math.MixedSingleBosonEvaluation.substitute_zero,
    ``Math.MixedSingleBosonEvaluation.pull_apply,
    ``Math.MixedSingleBosonEvaluation.pull_add,
    ``Math.MixedSingleBosonEvaluation.pull_smul,
    ``Math.MixedSingleBosonEvaluation.pull_zero,
    ``Math.MixedSingleBosonEvaluation.nonzero_of_probe,
    ``Math.MixedSingleBosonEvaluation.invariant_at_fixed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Symbolic coefficient bridge {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Symbolic coefficient bridge: layer and {ds.length} strict transitive checks passed"
