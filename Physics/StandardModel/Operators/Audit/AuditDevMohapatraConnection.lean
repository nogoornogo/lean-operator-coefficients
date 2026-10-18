import Physics.StandardModel.Operators.DevMohapatraConnection
import Physics.StandardModel.Operators.DevMohapatraPhysicalSource
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dev connection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraConnection.F,
    ``GUT.DevMohapatraConnection.H,
    ``GUT.DevMohapatraConnection.residual,
    ``GUT.DevMohapatraConnection.action,
    ``GUT.DevMohapatraConnection.physical_invariant,
    ``GUT.DevMohapatraConnection.up_action,
    ``GUT.DevMohapatraConnection.down_action,
    ``GUT.DevMohapatraConnection.spin,
    ``GUT.DevMohapatraConnection.spin_invariant,
    ``GUT.DevMohapatraConnection.printed,
    ``GUT.DevMohapatraConnection.printed_invariant,
    ``GUT.DevMohapatraConnection.printed_apply,
    ``GUT.DevMohapatraConnection.project,
    ``GUT.DevMohapatraConnection.project_pure,
    ``GUT.DevMohapatraConnection.flavored,
    ``GUT.DevMohapatraConnection.flavored_pure,
    ``GUT.DevMohapatraConnection.project_action,
    ``GUT.DevMohapatraConnection.flavored_invariant,
    ``GUT.DevMohapatraConnection.downCoupling,
    ``GUT.DevMohapatraConnection.downCoupling_swap,
    ``GUT.DevMohapatraConnection.downCoupling_same,
    ``GUT.DevMohapatraConnection.downCoupling_selected,
    ``GUT.DevMohapatraConnection.printed_evaluation,
    ``GUT.DevMohapatraConnection.QF,
    ``GUT.DevMohapatraConnection.FC,
    ``GUT.DevMohapatraConnection.orderedLift,
    ``GUT.DevMohapatraConnection.orderedLift_apply,
    ``GUT.DevMohapatraConnection.sourceExterior,
    ``GUT.DevMohapatraConnection.probe,
    ``GUT.DevMohapatraConnection.sourceExterior_evaluation,
    ``GUT.DevMohapatraConnection.sourceExterior_invariant,
    ``GUT.DevMohapatraConnection.sourceExterior_nonzero,
    ``GUT.DevMohapatraConnection.weighted_nonzero_iff,
    ``GUT.DevMohapatraPhysicalSource.P,
    ``GUT.DevMohapatraPhysicalSource.Field,
    ``GUT.DevMohapatraPhysicalSource.rho,
    ``GUT.DevMohapatraPhysicalSource.reorder,
    ``GUT.DevMohapatraPhysicalSource.source,
    ``GUT.DevMohapatraPhysicalSource.coefficient,
    ``GUT.DevMohapatraPhysicalSource.selected,
    ``GUT.DevMohapatraPhysicalSource.evaluation,
    ``GUT.DevMohapatraPhysicalSource.nonzero,
    ``GUT.DevMohapatraPhysicalSource.domain,
    ``GUT.DevMohapatraPhysicalSource.satisfies]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dev connection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dev connection: {ds.length} strict transitive checks passed"
