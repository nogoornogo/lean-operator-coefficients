import Physics.StandardModel.Operators.SMWeylExtractionInput
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM Weyl input audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMWeylExtractionInput.kernel_dimension_int, ``GUT.SMWeylExtractionInput.multiplicity_nonnegative,
    ``GUT.SMWeylExtractionInput.kernel_dimension, ``GUT.SMWeylExtractionInput.multiplicity_le_columns,
    ``GUT.SMWeylExtractionInput.rank_formula, ``GUT.SMWeylExtractionInput.local_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM Weyl input audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM Weyl input audit: layer and {ds.length} strict transitive conditional checks passed"
