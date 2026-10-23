import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Physics.FieldTheory.Jets.HiggsFieldDictionary
import Physics.FieldTheory.Jets.HiggsLagrangianInput
import Math.RepresentationTheory.HiggsInternalSymmetry
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsStandardInput.Group => Physics.HiggsStandardInput.Group,
  GUT.HiggsStandardInput.action => Physics.HiggsStandardInput.action,
  GUT.HiggsStandardInput.coefficientEquiv => Physics.HiggsStandardInput.coefficientEquiv,
  GUT.HiggsStandardInput.covariance => Physics.HiggsStandardInput.covariance,
  GUT.HiggsStandardInput.direct => Physics.HiggsStandardInput.direct,
  GUT.HiggsStandardInput.directions => Physics.HiggsStandardInput.directions,
  GUT.HiggsStandardInput.extraction => Physics.HiggsStandardInput.extraction,
  GUT.HiggsStandardInput.factorize => Physics.HiggsStandardInput.factorize,
  GUT.HiggsStandardInput.fields => Physics.HiggsStandardInput.fields,
  GUT.HiggsStandardInput.forgetSymmetries => Physics.HiggsStandardInput.forgetSymmetries,
  GUT.HiggsStandardInput.generated_stable => Physics.HiggsStandardInput.generated_stable,
  GUT.HiggsStandardInput.higgs_relation => Physics.HiggsStandardInput.higgs_relation,
  GUT.HiggsStandardInput.ideal_stable => Physics.HiggsStandardInput.ideal_stable,
  GUT.HiggsStandardInput.input => Physics.HiggsStandardInput.input,
  GUT.HiggsStandardInput.jets => Physics.HiggsStandardInput.jets,
  GUT.HiggsStandardInput.stable => Physics.HiggsStandardInput.stable,
  GUT.HiggsStandardInput.toDirect => Physics.HiggsStandardInput.toDirect,
  GUT.HiggsStandardInput.toGenerated => Physics.HiggsStandardInput.toGenerated,
  GUT.HiggsStandardInput.transport => Physics.HiggsStandardInput.transport
]

assert_compatible GUT.HiggsStandardInput.Group => Physics.HiggsStandardInput.Group
assert_compatible GUT.HiggsStandardInput.action => Physics.HiggsStandardInput.action
assert_compatible GUT.HiggsStandardInput.coefficientEquiv => Physics.HiggsStandardInput.coefficientEquiv
assert_compatible GUT.HiggsStandardInput.covariance => Physics.HiggsStandardInput.covariance
assert_compatible GUT.HiggsStandardInput.direct => Physics.HiggsStandardInput.direct
assert_compatible GUT.HiggsStandardInput.directions => Physics.HiggsStandardInput.directions
assert_compatible GUT.HiggsStandardInput.extraction => Physics.HiggsStandardInput.extraction
assert_compatible GUT.HiggsStandardInput.factorize => Physics.HiggsStandardInput.factorize
assert_compatible GUT.HiggsStandardInput.fields => Physics.HiggsStandardInput.fields
assert_compatible GUT.HiggsStandardInput.forgetSymmetries => Physics.HiggsStandardInput.forgetSymmetries
assert_compatible GUT.HiggsStandardInput.generated_stable => Physics.HiggsStandardInput.generated_stable
assert_compatible GUT.HiggsStandardInput.higgs_relation => Physics.HiggsStandardInput.higgs_relation
assert_compatible GUT.HiggsStandardInput.ideal_stable => Physics.HiggsStandardInput.ideal_stable
assert_compatible GUT.HiggsStandardInput.input => Physics.HiggsStandardInput.input
assert_compatible GUT.HiggsStandardInput.jets => Physics.HiggsStandardInput.jets
assert_compatible GUT.HiggsStandardInput.stable => Physics.HiggsStandardInput.stable
assert_compatible GUT.HiggsStandardInput.toDirect => Physics.HiggsStandardInput.toDirect
assert_compatible GUT.HiggsStandardInput.toGenerated => Physics.HiggsStandardInput.toGenerated
assert_compatible GUT.HiggsStandardInput.transport => Physics.HiggsStandardInput.transport
