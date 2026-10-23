import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraConnection
import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraPhysicalSource
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dev connection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraConnection.F,
    ``Physics.DevMohapatraConnection.H,
    ``Physics.DevMohapatraConnection.residual,
    ``Physics.DevMohapatraConnection.action,
    ``Physics.DevMohapatraConnection.physical_invariant,
    ``Physics.DevMohapatraConnection.up_action,
    ``Physics.DevMohapatraConnection.down_action,
    ``Physics.DevMohapatraConnection.spin,
    ``Physics.DevMohapatraConnection.spin_invariant,
    ``Physics.DevMohapatraConnection.printed,
    ``Physics.DevMohapatraConnection.printed_invariant,
    ``Physics.DevMohapatraConnection.printed_apply,
    ``Physics.DevMohapatraConnection.project,
    ``Physics.DevMohapatraConnection.project_pure,
    ``Physics.DevMohapatraConnection.flavored,
    ``Physics.DevMohapatraConnection.flavored_pure,
    ``Physics.DevMohapatraConnection.project_action,
    ``Physics.DevMohapatraConnection.flavored_invariant,
    ``Physics.DevMohapatraConnection.downCoupling,
    ``Physics.DevMohapatraConnection.downCoupling_swap,
    ``Physics.DevMohapatraConnection.downCoupling_same,
    ``Physics.DevMohapatraConnection.downCoupling_selected,
    ``Physics.DevMohapatraConnection.printed_evaluation,
    ``Physics.DevMohapatraConnection.QF,
    ``Physics.DevMohapatraConnection.FC,
    ``Physics.DevMohapatraConnection.orderedLift,
    ``Physics.DevMohapatraConnection.orderedLift_apply,
    ``Physics.DevMohapatraConnection.sourceExterior,
    ``Physics.DevMohapatraConnection.probe,
    ``Physics.DevMohapatraConnection.sourceExterior_evaluation,
    ``Physics.DevMohapatraConnection.sourceExterior_invariant,
    ``Physics.DevMohapatraConnection.sourceExterior_nonzero,
    ``Physics.DevMohapatraConnection.weighted_nonzero_iff,
    ``Physics.DevMohapatraPhysicalSource.P,
    ``Physics.DevMohapatraPhysicalSource.Field,
    ``Physics.DevMohapatraPhysicalSource.rho,
    ``Physics.DevMohapatraPhysicalSource.reorder,
    ``Physics.DevMohapatraPhysicalSource.source,
    ``Physics.DevMohapatraPhysicalSource.coefficient,
    ``Physics.DevMohapatraPhysicalSource.selected,
    ``Physics.DevMohapatraPhysicalSource.evaluation,
    ``Physics.DevMohapatraPhysicalSource.nonzero,
    ``Physics.DevMohapatraPhysicalSource.domain,
    ``Physics.DevMohapatraPhysicalSource.satisfies]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dev connection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dev connection: {ds.length} strict transitive checks passed"
