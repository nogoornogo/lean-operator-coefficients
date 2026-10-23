import Physics.StandardModel.Operators.Support.Decomposition.SMComputableSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "computable SM audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMComputableSlotWeights.monomial_zero, ``Physics.SMComputableSlotWeights.monomial_add,
    ``Physics.SMComputableSlotWeights.monomial_inverse, ``Physics.SMComputableSlotWeights.gauge_eigen,
    ``Physics.SMComputableSlotWeights.spin_eigen, ``Physics.SMComputableSlotWeights.field_eigen,
    ``Physics.SMComputableCharacter.slot_eigen, ``Physics.SMComputableCharacter.exterior_evaluation,
    ``Physics.SMComputableCharacter.source_evaluation, ``Physics.SMComputableCharacter.boson_evaluation,
    ``Physics.SMComputableCharacter.terms_evaluation, ``Physics.SMComputableCharacter.polynomial_coefficient,
    ``Physics.SMComputableCharacter.extraction_eq, ``Physics.SMComputableSupport.presents,
    ``Physics.SMComputableSupport.kernel_dimension_int, ``Physics.SMComputableSupport.kernel_dimension,
    ``Physics.SMComputableSupport.nonnegative, ``Physics.SMComputableSupport.rank_formula,
    ``Physics.SMComputableSupport.local_allowed_iff, ``Physics.SMComputableQLSupport.test_allowed_iff,
    ``Physics.SMComputableQLSupport.original_allowed_iff, ``Physics.SMComputableQLSupport.original_forbidden_iff,
    ``Physics.SMComputableQLSupport.entry_allowed_iff, ``Physics.SMComputableQLSupport.allowed_iff,
    ``Physics.SMComputableQLSupport.forbidden_iff, ``Physics.SMComputableQLSupport.satisfies_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "computable SM audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"computable SM audit: layer and {ds.length} strict transitive checks passed; Weyl consumers remain conditional"
