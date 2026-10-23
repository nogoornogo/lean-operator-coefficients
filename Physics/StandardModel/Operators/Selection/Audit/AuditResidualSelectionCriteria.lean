import Physics.StandardModel.Operators.Selection.CyclicResidualSelection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Residual selection imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.ResidualSelectionCriteria.deltaLOne,
    ``Physics.ResidualSelectionCriteria.deltaBTwo, ``Physics.ResidualSelectionCriteria.weinberg,
    ``Physics.ResidualSelectionCriteria.dipole, ``Physics.ResidualSelectionCriteria.deltaLOne_forbidden_iff,
    ``Physics.ScalarResidualSelection.scalar_formula, ``Physics.ScalarResidualSelection.coefficient,
    ``Physics.ScalarResidualSelection.allowed_four, ``Physics.ScalarResidualSelection.allowed_qque,
    ``Physics.ScalarResidualSelection.allowed_qqql, ``Physics.ScalarResidualSelection.allowed_total,
    ``Physics.CyclicResidualSelection.signedCharges, ``Physics.CyclicResidualSelection.flavor,
    ``Physics.CyclicResidualSelection.familyCharge, ``Physics.CyclicResidualSelection.neutral_four_iff,
    ``Physics.CyclicResidualSelection.allowed_total_iff,
    ``Physics.CyclicResidualSelection.allowed_family_iff,
    ``Physics.CyclicResidualSelection.forbidden_family_iff,
    ``Physics.CyclicResidualSelection.forbidden_total_iff,
    ``Physics.CyclicResidualSelection.allowed_weinberg_iff,
    ``Physics.CyclicResidualSelection.simultaneous_iff,
    ``Physics.CyclicResidualSelection.quarkParity_conditions,
    ``Physics.CyclicResidualSelection.quarkParity_selection,
    ``Physics.CyclicResidualSelection.trivial_assignment_rejected,
    ``Physics.CyclicResidualSelection.order_one_rejected]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual selection: {ds.length} strict transitive checks passed"
