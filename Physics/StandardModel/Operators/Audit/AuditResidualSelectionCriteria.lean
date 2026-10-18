import Physics.StandardModel.Operators.CyclicResidualSelection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Residual selection imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.ResidualSelectionCriteria.deltaLOne,
    ``GUT.ResidualSelectionCriteria.deltaBTwo, ``GUT.ResidualSelectionCriteria.weinberg,
    ``GUT.ResidualSelectionCriteria.dipole, ``GUT.ResidualSelectionCriteria.deltaLOne_forbidden_iff,
    ``GUT.ScalarResidualSelection.scalar_formula, ``GUT.ScalarResidualSelection.coefficient,
    ``GUT.ScalarResidualSelection.allowed_four, ``GUT.ScalarResidualSelection.allowed_qque,
    ``GUT.ScalarResidualSelection.allowed_qqql, ``GUT.ScalarResidualSelection.allowed_total,
    ``GUT.CyclicResidualSelection.signedCharges, ``GUT.CyclicResidualSelection.flavor,
    ``GUT.CyclicResidualSelection.familyCharge, ``GUT.CyclicResidualSelection.neutral_four_iff,
    ``GUT.CyclicResidualSelection.allowed_total_iff,
    ``GUT.CyclicResidualSelection.allowed_family_iff,
    ``GUT.CyclicResidualSelection.forbidden_family_iff,
    ``GUT.CyclicResidualSelection.forbidden_total_iff,
    ``GUT.CyclicResidualSelection.allowed_weinberg_iff,
    ``GUT.CyclicResidualSelection.simultaneous_iff,
    ``GUT.CyclicResidualSelection.quarkParity_conditions,
    ``GUT.CyclicResidualSelection.quarkParity_selection,
    ``GUT.CyclicResidualSelection.trivial_assignment_rejected,
    ``GUT.CyclicResidualSelection.order_one_rejected]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual selection: {ds.length} strict transitive checks passed"
