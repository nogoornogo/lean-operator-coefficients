import Physics.StandardModel.Operators.DeltaBTwoCyclicSelection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Delta-B-two selection imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DeltaBTwoScalarSelection.total,
    ``GUT.DeltaBTwoScalarSelection.Neutral,
    ``GUT.DeltaBTwoScalarSelection.scalar_map,
    ``GUT.DeltaBTwoScalarSelection.slot_action,
    ``GUT.DeltaBTwoScalarSelection.residual_action,
    ``GUT.DeltaBTwoScalarSelection.neutral_invariant,
    ``GUT.DeltaBTwoScalarSelection.coefficientEquiv,
    ``GUT.DeltaBTwoScalarSelection.twoProbeEquiv,
    ``GUT.DeltaBTwoScalarSelection.pairEquiv,
    ``GUT.DeltaBTwoScalarSelection.reconstruct_twoProbes,
    ``GUT.DeltaBTwoScalarSelection.allowed_iff,
    ``GUT.DeltaBTwoScalarSelection.forbidden_iff,
    ``GUT.DeltaBTwoScalarSelection.finrank_neutral,
    ``GUT.DeltaBTwoScalarSelection.inverse_twoProbes,
    ``GUT.DeltaBTwoScalarSelection.onFieldsTwoProbeEquiv,
    ``GUT.DeltaBTwoScalarSelection.allowed_onFields_iff,
    ``GUT.DeltaBTwoScalarSelection.forbidden_onFields_iff,
    ``GUT.DeltaBTwoCyclicSelection.charge,
    ``GUT.DeltaBTwoCyclicSelection.neutral_iff,
    ``GUT.DeltaBTwoCyclicSelection.allowed_iff,
    ``GUT.DeltaBTwoCyclicSelection.forbidden_iff,
    ``GUT.DeltaBTwoCyclicSelection.twoProbeEquiv,
    ``GUT.DeltaBTwoCyclicSelection.simultaneous_iff,
    ``GUT.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff,
    ``GUT.DeltaBTwoCyclicSelection.quarkParity_allowed,
    ``GUT.DeltaBTwoCyclicSelection.forbidBoth_conditions,
    ``GUT.DeltaBTwoCyclicSelection.forbidBoth_selection,
    ``GUT.DeltaBTwoCyclicSelection.trivial_allowed,
    ``GUT.DeltaBTwoCyclicSelection.order_one_allowed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B-two selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B-two selection: {ds.length} strict transitive checks passed"
