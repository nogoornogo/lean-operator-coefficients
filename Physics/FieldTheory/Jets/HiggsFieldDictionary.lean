import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsFieldDictionary
import Math.RepresentationTheory.PairedComponentFields
import Physics.StandardModel.Gauge.SMGaugeConjugation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.Inputs.HiggsFieldDictionary instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFieldDictionary.ConjugateValues => Physics.HiggsFieldDictionary.ConjugateValues,
  GUT.HiggsFieldDictionary.Fields => Physics.HiggsFieldDictionary.Fields,
  GUT.HiggsFieldDictionary.Labels => Physics.HiggsFieldDictionary.Labels,
  GUT.HiggsFieldDictionary.V => Physics.HiggsFieldDictionary.V,
  GUT.HiggsFieldDictionary.action => Physics.HiggsFieldDictionary.action,
  GUT.HiggsFieldDictionary.components => Physics.HiggsFieldDictionary.components,
  GUT.HiggsFieldDictionary.components_action => Physics.HiggsFieldDictionary.components_action,
  GUT.HiggsFieldDictionary.components_apply => Physics.HiggsFieldDictionary.components_apply,
  GUT.HiggsFieldDictionary.conjugateValues_stable => Physics.HiggsFieldDictionary.conjugateValues_stable,
  GUT.HiggsFieldDictionary.conjugate_action => Physics.HiggsFieldDictionary.conjugate_action,
  GUT.HiggsFieldDictionary.higgs => Physics.HiggsFieldDictionary.higgs,
  GUT.HiggsFieldDictionary.pairing => Physics.HiggsFieldDictionary.pairing,
  GUT.HiggsFieldDictionary.pairing_conjugate => Physics.HiggsFieldDictionary.pairing_conjugate,
  GUT.HiggsFieldDictionary.pairing_coordinates => Physics.HiggsFieldDictionary.pairing_coordinates,
  GUT.HiggsFieldDictionary.pairing_invariant => Physics.HiggsFieldDictionary.pairing_invariant
]

assert_compatible GUT.HiggsFieldDictionary.ConjugateValues => Physics.HiggsFieldDictionary.ConjugateValues
assert_compatible GUT.HiggsFieldDictionary.Fields => Physics.HiggsFieldDictionary.Fields
assert_compatible GUT.HiggsFieldDictionary.Labels => Physics.HiggsFieldDictionary.Labels
assert_compatible GUT.HiggsFieldDictionary.V => Physics.HiggsFieldDictionary.V
assert_compatible GUT.HiggsFieldDictionary.action => Physics.HiggsFieldDictionary.action
assert_compatible GUT.HiggsFieldDictionary.components => Physics.HiggsFieldDictionary.components
assert_compatible GUT.HiggsFieldDictionary.components_action => Physics.HiggsFieldDictionary.components_action
assert_compatible GUT.HiggsFieldDictionary.components_apply => Physics.HiggsFieldDictionary.components_apply
assert_compatible GUT.HiggsFieldDictionary.conjugateValues_stable => Physics.HiggsFieldDictionary.conjugateValues_stable
assert_compatible GUT.HiggsFieldDictionary.conjugate_action => Physics.HiggsFieldDictionary.conjugate_action
assert_compatible GUT.HiggsFieldDictionary.higgs => Physics.HiggsFieldDictionary.higgs
assert_compatible GUT.HiggsFieldDictionary.pairing => Physics.HiggsFieldDictionary.pairing
assert_compatible GUT.HiggsFieldDictionary.pairing_conjugate => Physics.HiggsFieldDictionary.pairing_conjugate
assert_compatible GUT.HiggsFieldDictionary.pairing_coordinates => Physics.HiggsFieldDictionary.pairing_coordinates
assert_compatible GUT.HiggsFieldDictionary.pairing_invariant => Physics.HiggsFieldDictionary.pairing_invariant
