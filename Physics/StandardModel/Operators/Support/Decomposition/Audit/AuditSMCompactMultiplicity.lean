import Physics.StandardModel.Operators.Support.Decomposition.SMCompactMultiplicity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM compact multiplicity audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMCombinedCompactAction.field_gauge, ``Physics.SMCombinedCompactAction.field_spin,
    ``Physics.SMCombinedCompactAction.source_gauge, ``Physics.SMCombinedCompactAction.source_spin,
    ``Physics.SMCombinedCompactAction.action_gauge, ``Physics.SMCombinedCompactAction.action_spin,
    ``Physics.SMCombinedCompactAction.coefficientEquiv, ``Physics.SMCombinedCompactContinuity.color_coefficients,
    ``Physics.SMCombinedCompactContinuity.weak_coefficients, ``Physics.SMCombinedCompactContinuity.phase_continuous,
    ``Physics.SMCombinedCompactContinuity.twist_coefficients, ``Physics.SMCombinedCompactContinuity.gauge_coefficients,
    ``Physics.SMCombinedCompactContinuity.spin_coefficients, ``Physics.SMCombinedCompactContinuity.field_coefficients,
    ``Physics.SMCombinedCompactContinuity.source_continuous, ``Physics.SMCombinedCompactContinuity.bosonEquiv,
    ``Physics.SMCombinedCompactContinuity.boson_continuous, ``Physics.SMCombinedCompactContinuity.equiv,
    ``Physics.SMCombinedCompactContinuity.continuous_model, ``Physics.SMCombinedCompactContinuity.coefficientEquiv,
    ``Physics.SMCompactTorus.color_mem, ``Physics.SMCompactTorus.color, ``Physics.SMCompactTorus.color_continuous,
    ``Physics.SMCompactTorus.inclusion, ``Physics.SMCompactMultiplicity.polynomial, ``Physics.SMCompactMultiplicity.presents,
    ``Physics.SMCompactMultiplicity.kernel_dimension_int, ``Physics.SMCompactMultiplicity.nonnegative,
    ``Physics.SMCompactMultiplicity.kernel_dimension, ``Physics.SMCompactMultiplicity.rank_formula,
    ``Physics.SMCompactMultiplicity.local_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM compact multiplicity audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM compact multiplicity audit: layer and {ds.length} strict transitive checks passed; extraction remains conditional"
