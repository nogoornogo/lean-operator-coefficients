import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoCyclicSelection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Delta-B-two selection imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DeltaBTwoScalarSelection.total,
    ``Physics.DeltaBTwoScalarSelection.Neutral,
    ``Physics.DeltaBTwoScalarSelection.scalar_map,
    ``Physics.DeltaBTwoScalarSelection.slot_action,
    ``Physics.DeltaBTwoScalarSelection.residual_action,
    ``Physics.DeltaBTwoScalarSelection.neutral_invariant,
    ``Physics.DeltaBTwoScalarSelection.coefficientEquiv,
    ``Physics.DeltaBTwoScalarSelection.twoProbeEquiv,
    ``Physics.DeltaBTwoScalarSelection.pairEquiv,
    ``Physics.DeltaBTwoScalarSelection.reconstruct_twoProbes,
    ``Physics.DeltaBTwoScalarSelection.allowed_iff,
    ``Physics.DeltaBTwoScalarSelection.forbidden_iff,
    ``Physics.DeltaBTwoScalarSelection.finrank_neutral,
    ``Physics.DeltaBTwoScalarSelection.inverse_twoProbes,
    ``Physics.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv,
    ``Physics.DeltaBTwoScalarSelection.allowed_onFields_iff,
    ``Physics.DeltaBTwoScalarSelection.forbidden_onFields_iff,
    ``Physics.DeltaBTwoCyclicSelection.charge,
    ``Physics.DeltaBTwoCyclicSelection.neutral_iff,
    ``Physics.DeltaBTwoCyclicSelection.allowed_iff,
    ``Physics.DeltaBTwoCyclicSelection.forbidden_iff,
    ``Physics.DeltaBTwoCyclicSelection.twoProbeEquiv,
    ``Physics.DeltaBTwoCyclicSelection.simultaneous_iff,
    ``Physics.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff,
    ``Physics.DeltaBTwoCyclicSelection.quarkParity_allowed,
    ``Physics.DeltaBTwoCyclicSelection.forbidBoth_conditions,
    ``Physics.DeltaBTwoCyclicSelection.forbidBoth_selection,
    ``Physics.DeltaBTwoCyclicSelection.trivial_allowed,
    ``Physics.DeltaBTwoCyclicSelection.order_one_allowed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B-two selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B-two selection: {ds.length} strict transitive checks passed"
