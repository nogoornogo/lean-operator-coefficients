import Physics.StandardModel.Operators.SMCompactMultiplicity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM compact multiplicity audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMCombinedCompactAction.field_gauge, ``GUT.SMCombinedCompactAction.field_spin,
    ``GUT.SMCombinedCompactAction.source_gauge, ``GUT.SMCombinedCompactAction.source_spin,
    ``GUT.SMCombinedCompactAction.action_gauge, ``GUT.SMCombinedCompactAction.action_spin,
    ``GUT.SMCombinedCompactAction.coefficientEquiv, ``GUT.SMCombinedCompactContinuity.color_coefficients,
    ``GUT.SMCombinedCompactContinuity.weak_coefficients, ``GUT.SMCombinedCompactContinuity.phase_continuous,
    ``GUT.SMCombinedCompactContinuity.twist_coefficients, ``GUT.SMCombinedCompactContinuity.gauge_coefficients,
    ``GUT.SMCombinedCompactContinuity.spin_coefficients, ``GUT.SMCombinedCompactContinuity.field_coefficients,
    ``GUT.SMCombinedCompactContinuity.source_continuous, ``GUT.SMCombinedCompactContinuity.bosonEquiv,
    ``GUT.SMCombinedCompactContinuity.boson_continuous, ``GUT.SMCombinedCompactContinuity.equiv,
    ``GUT.SMCombinedCompactContinuity.continuous_model, ``GUT.SMCombinedCompactContinuity.coefficientEquiv,
    ``GUT.SMCompactTorus.color_mem, ``GUT.SMCompactTorus.color, ``GUT.SMCompactTorus.color_continuous,
    ``GUT.SMCompactTorus.inclusion, ``GUT.SMCompactMultiplicity.polynomial, ``GUT.SMCompactMultiplicity.presents,
    ``GUT.SMCompactMultiplicity.kernel_dimension_int, ``GUT.SMCompactMultiplicity.nonnegative,
    ``GUT.SMCompactMultiplicity.kernel_dimension, ``GUT.SMCompactMultiplicity.rank_formula,
    ``GUT.SMCompactMultiplicity.local_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM compact multiplicity audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM compact multiplicity audit: layer and {ds.length} strict transitive checks passed; extraction remains conditional"
