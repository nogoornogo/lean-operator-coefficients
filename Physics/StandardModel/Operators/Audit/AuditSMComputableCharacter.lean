import Physics.StandardModel.Operators.SMComputableSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "computable SM audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMComputableSlotWeights.monomial_zero, ``GUT.SMComputableSlotWeights.monomial_add,
    ``GUT.SMComputableSlotWeights.monomial_inverse, ``GUT.SMComputableSlotWeights.gauge_eigen,
    ``GUT.SMComputableSlotWeights.spin_eigen, ``GUT.SMComputableSlotWeights.field_eigen,
    ``GUT.SMComputableCharacter.slot_eigen, ``GUT.SMComputableCharacter.exterior_evaluation,
    ``GUT.SMComputableCharacter.source_evaluation, ``GUT.SMComputableCharacter.boson_evaluation,
    ``GUT.SMComputableCharacter.terms_evaluation, ``GUT.SMComputableCharacter.polynomial_coefficient,
    ``GUT.SMComputableCharacter.extraction_eq, ``GUT.SMComputableSupport.presents,
    ``GUT.SMComputableSupport.kernel_dimension_int, ``GUT.SMComputableSupport.kernel_dimension,
    ``GUT.SMComputableSupport.nonnegative, ``GUT.SMComputableSupport.rank_formula,
    ``GUT.SMComputableSupport.local_allowed_iff, ``GUT.SMComputableQLSupport.test_allowed_iff,
    ``GUT.SMComputableQLSupport.original_allowed_iff, ``GUT.SMComputableQLSupport.original_forbidden_iff,
    ``GUT.SMComputableQLSupport.entry_allowed_iff, ``GUT.SMComputableQLSupport.allowed_iff,
    ``GUT.SMComputableQLSupport.forbidden_iff, ``GUT.SMComputableQLSupport.satisfies_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "computable SM audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"computable SM audit: layer and {ds.length} strict transitive checks passed; Weyl consumers remain conditional"
