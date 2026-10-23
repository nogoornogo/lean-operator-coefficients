import Physics.StandardModel.Operators.Support.Coordinates.SMCoefficientAssembly
import Physics.StandardModel.Operators.Support.Coordinates.SMGroupedCharacter
import Physics.StandardModel.Operators.Support.Coordinates.SMHiggsStringExtraction
import Physics.StandardModel.Operators.Support.Coordinates.SMKernelWeightData
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "sparse SM audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMCoefficientAssembly.factor,
    ``Physics.SMGroupedCharacter.boundedCoefficient_eq,
    ``Physics.SMGroupedCharacter.solveBounded_eq,
    ``Physics.SMGroupedCharacter.groups_verified,
    ``Physics.SMGroupedCharacter.source_coefficient,
    ``Physics.SMGroupedCharacter.solveGrouped_eq,
    ``Physics.SMSparseCharacter.unpack_pack, ``Physics.SMSparseCharacter.pack_unpack,
    ``Physics.SMSparseCharacter.terms_evaluation_general, ``Physics.SMSparseCharacter.terms_evaluation,
    ``Physics.SMSparseCharacter.coefficient_reference, ``Physics.SMSparseCharacter.tables_lookup,
    ``Physics.SMSparseCharacter.cached_evaluation_general, ``Physics.SMSparseCharacter.cached_coefficient,
    ``Physics.SMSparseCharacter.cached_multiplicity, ``Physics.SMSparseCharacter.presents,
    ``Physics.SMSparseCharacter.polynomial_coefficient, ``Physics.SMSparseCharacter.extractAt_pack,
    ``Physics.SMSparseCharacter.extraction_eq, ``Physics.SMSparseCharacter.polynomial_reference,
    ``Physics.SMSparseCharacter.multiplicity_reference,
    ``Physics.SMSparseSupport.kernel_dimension_int, ``Physics.SMSparseSupport.kernel_dimension,
    ``Physics.SMSparseSupport.rank_formula, ``Physics.SMSparseSupport.local_allowed_iff,
    ``Physics.SMSparseQLSupport.test_reference, ``Physics.SMSparseQLSupport.test_allowed_iff,
    ``Physics.SMSparseQLSupport.original_allowed_iff,
    ``Physics.SMNeutralSparseRanks.input_count, ``Physics.SMNeutralSparseRanks.inputs_enumerated,
    ``Physics.SMNeutralSparseRanks.counts_pattern, ``Physics.SMNeutralSparseRanks.solve_multiplicity,
    ``Physics.SMNeutralSparseRanks.kernel_dimension, ``Physics.SMNeutralSparseRanks.rank_sound,
    ``Physics.SMHiggsStringExtraction.packed_reference, ``Physics.SMHiggsStringExtraction.cached_source,
    ``Physics.SMHiggsStringExtraction.coefficient_string, ``Physics.SMHiggsStringExtraction.multiplicity_eq,
    ``Physics.SMHiggsStringExtraction.keyMatches_eq, ``Physics.SMHiggsStringExtraction.lookup_eq,
    ``Physics.SMHiggsStringExtraction.a2Extract_eq, ``Physics.SMKernelWeightData.weights_verified,
    ``Physics.SMKernelWeightData.tables_verified, ``Physics.SMNeutralSparseRanks.solve_eq_of_value,
    ``Physics.SMNeutralSparseRanks.columnsFast_eq,
    ``Physics.SMNeutralSparseRanks.constant_source_row, ``Physics.SMNeutralSparseRanks.solveDirect_eq,
    ``Physics.SMNeutralSparseRanks.solveDirectWith_data]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "sparse SM audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"sparse SM audit: layer and {ds.length} strict transitive checks passed; Weyl consumers remain conditional"
