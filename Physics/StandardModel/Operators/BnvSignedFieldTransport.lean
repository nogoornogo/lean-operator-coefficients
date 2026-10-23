import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSignedFieldTransport
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Operators.BnvSevenNegativeTransport
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSignedFieldTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSignedFieldTransport.Reindexed => Physics.BnvSignedFieldTransport.Reindexed,
  GUT.BnvSignedFieldTransport.coefficientEquiv => Physics.BnvSignedFieldTransport.coefficientEquiv,
  GUT.BnvSignedFieldTransport.exterior => Physics.BnvSignedFieldTransport.exterior,
  GUT.BnvSignedFieldTransport.extract_mem => Physics.BnvSignedFieldTransport.extract_mem,
  GUT.BnvSignedFieldTransport.extract_pure => Physics.BnvSignedFieldTransport.extract_pure,
  GUT.BnvSignedFieldTransport.field => Physics.BnvSignedFieldTransport.field,
  GUT.BnvSignedFieldTransport.full => Physics.BnvSignedFieldTransport.full,
  GUT.BnvSignedFieldTransport.full_apply => Physics.BnvSignedFieldTransport.full_apply,
  GUT.BnvSignedFieldTransport.full_single => Physics.BnvSignedFieldTransport.full_single,
  GUT.BnvSignedFieldTransport.full_supported => Physics.BnvSignedFieldTransport.full_supported,
  GUT.BnvSignedFieldTransport.full_symm_single => Physics.BnvSignedFieldTransport.full_symm_single,
  GUT.BnvSignedFieldTransport.groupMap => Physics.BnvSignedFieldTransport.groupMap,
  GUT.BnvSignedFieldTransport.groupMap.eq_1 => Physics.BnvSignedFieldTransport.groupMap.eq_1,
  GUT.BnvSignedFieldTransport.groupMap_surjective => Physics.BnvSignedFieldTransport.groupMap_surjective,
  GUT.BnvSignedFieldTransport.lepton_opposite => Physics.BnvSignedFieldTransport.lepton_opposite,
  GUT.BnvSignedFieldTransport.localOpposite => Physics.BnvSignedFieldTransport.localOpposite,
  GUT.BnvSignedFieldTransport.localRelabel => Physics.BnvSignedFieldTransport.localRelabel,
  GUT.BnvSignedFieldTransport.negativeEquiv => Physics.BnvSignedFieldTransport.negativeEquiv,
  GUT.BnvSignedFieldTransport.opposite => Physics.BnvSignedFieldTransport.opposite,
  GUT.BnvSignedFieldTransport.opposite_degree => Physics.BnvSignedFieldTransport.opposite_degree,
  GUT.BnvSignedFieldTransport.opposite_twice => Physics.BnvSignedFieldTransport.opposite_twice,
  GUT.BnvSignedFieldTransport.reconstruct_mem => Physics.BnvSignedFieldTransport.reconstruct_mem,
  GUT.BnvSignedFieldTransport.reconstruct_pure => Physics.BnvSignedFieldTransport.reconstruct_pure,
  GUT.BnvSignedFieldTransport.reindexed => Physics.BnvSignedFieldTransport.reindexed,
  GUT.BnvSignedFieldTransport.sectorEquiv => Physics.BnvSignedFieldTransport.sectorEquiv
]

assert_compatible GUT.BnvSignedFieldTransport.Reindexed => Physics.BnvSignedFieldTransport.Reindexed
assert_compatible GUT.BnvSignedFieldTransport.coefficientEquiv => Physics.BnvSignedFieldTransport.coefficientEquiv
assert_compatible GUT.BnvSignedFieldTransport.exterior => Physics.BnvSignedFieldTransport.exterior
assert_compatible GUT.BnvSignedFieldTransport.extract_mem => Physics.BnvSignedFieldTransport.extract_mem
assert_compatible GUT.BnvSignedFieldTransport.extract_pure => Physics.BnvSignedFieldTransport.extract_pure
assert_compatible GUT.BnvSignedFieldTransport.field => Physics.BnvSignedFieldTransport.field
assert_compatible GUT.BnvSignedFieldTransport.full => Physics.BnvSignedFieldTransport.full
assert_compatible GUT.BnvSignedFieldTransport.full_apply => Physics.BnvSignedFieldTransport.full_apply
assert_compatible GUT.BnvSignedFieldTransport.full_single => Physics.BnvSignedFieldTransport.full_single
assert_compatible GUT.BnvSignedFieldTransport.full_supported => Physics.BnvSignedFieldTransport.full_supported
assert_compatible GUT.BnvSignedFieldTransport.full_symm_single => Physics.BnvSignedFieldTransport.full_symm_single
assert_compatible GUT.BnvSignedFieldTransport.groupMap => Physics.BnvSignedFieldTransport.groupMap
assert_compatible GUT.BnvSignedFieldTransport.groupMap.eq_1 => Physics.BnvSignedFieldTransport.groupMap.eq_1
assert_compatible GUT.BnvSignedFieldTransport.groupMap_surjective => Physics.BnvSignedFieldTransport.groupMap_surjective
assert_compatible GUT.BnvSignedFieldTransport.lepton_opposite => Physics.BnvSignedFieldTransport.lepton_opposite
assert_compatible GUT.BnvSignedFieldTransport.localOpposite => Physics.BnvSignedFieldTransport.localOpposite
assert_compatible GUT.BnvSignedFieldTransport.localRelabel => Physics.BnvSignedFieldTransport.localRelabel
assert_compatible GUT.BnvSignedFieldTransport.negativeEquiv => Physics.BnvSignedFieldTransport.negativeEquiv
assert_compatible GUT.BnvSignedFieldTransport.opposite => Physics.BnvSignedFieldTransport.opposite
assert_compatible GUT.BnvSignedFieldTransport.opposite_degree => Physics.BnvSignedFieldTransport.opposite_degree
assert_compatible GUT.BnvSignedFieldTransport.opposite_twice => Physics.BnvSignedFieldTransport.opposite_twice
assert_compatible GUT.BnvSignedFieldTransport.reconstruct_mem => Physics.BnvSignedFieldTransport.reconstruct_mem
assert_compatible GUT.BnvSignedFieldTransport.reconstruct_pure => Physics.BnvSignedFieldTransport.reconstruct_pure
assert_compatible GUT.BnvSignedFieldTransport.reindexed => Physics.BnvSignedFieldTransport.reindexed
assert_compatible GUT.BnvSignedFieldTransport.sectorEquiv => Physics.BnvSignedFieldTransport.sectorEquiv
