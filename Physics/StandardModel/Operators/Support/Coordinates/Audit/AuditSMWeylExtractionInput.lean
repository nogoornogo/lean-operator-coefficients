import Physics.StandardModel.Operators.Support.Coordinates.SMWeylExtractionInput
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM Weyl input audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMWeylExtractionInput.kernel_dimension_int, ``Physics.SMWeylExtractionInput.multiplicity_nonnegative,
    ``Physics.SMWeylExtractionInput.kernel_dimension, ``Physics.SMWeylExtractionInput.multiplicity_le_columns,
    ``Physics.SMWeylExtractionInput.rank_formula, ``Physics.SMWeylExtractionInput.local_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM Weyl input audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM Weyl input audit: layer and {ds.length} strict transitive conditional checks passed"
