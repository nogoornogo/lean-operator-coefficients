import Physics.StandardModel.Operators.Support.Joint.SMMixedConjugation
import Physics.StandardModel.Operators.SMSignedHiggsSupport
import Math.RepresentationTheory.PatternSpeciesRestriction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedConjugation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvLocalConjugation.opposite.eq_1 => Physics.BnvLocalConjugation.opposite.eq_1,
  GUT.SMMixedConjugation.actionEquiv => Physics.SMMixedConjugation.actionEquiv,
  GUT.SMMixedConjugation.bound_eq => Physics.SMMixedConjugation.bound_eq,
  GUT.SMMixedConjugation.charge_opposite => Physics.SMMixedConjugation.charge_opposite,
  GUT.SMMixedConjugation.coefficientEquiv => Physics.SMMixedConjugation.coefficientEquiv,
  GUT.SMMixedConjugation.local_higgs_iff => Physics.SMMixedConjugation.local_higgs_iff,
  GUT.SMMixedConjugation.local_higgs_transport => Physics.SMMixedConjugation.local_higgs_transport,
  GUT.SMMixedConjugation.oppositeEquiv => Physics.SMMixedConjugation.oppositeEquiv,
  GUT.SMMixedConjugation.original_ql_iff => Physics.SMMixedConjugation.original_ql_iff,
  GUT.SMMixedConjugation.signed_charge_opposite => Physics.SMMixedConjugation.signed_charge_opposite,
  GUT.SMMixedConjugation.sourceEquiv => Physics.SMMixedConjugation.sourceEquiv
]

assert_compatible GUT.BnvLocalConjugation.opposite.eq_1 => Physics.BnvLocalConjugation.opposite.eq_1
assert_compatible GUT.SMMixedConjugation.actionEquiv => Physics.SMMixedConjugation.actionEquiv
assert_compatible GUT.SMMixedConjugation.bound_eq => Physics.SMMixedConjugation.bound_eq
assert_compatible GUT.SMMixedConjugation.charge_opposite => Physics.SMMixedConjugation.charge_opposite
assert_compatible GUT.SMMixedConjugation.coefficientEquiv => Physics.SMMixedConjugation.coefficientEquiv
assert_compatible GUT.SMMixedConjugation.local_higgs_iff => Physics.SMMixedConjugation.local_higgs_iff
assert_compatible GUT.SMMixedConjugation.local_higgs_transport => Physics.SMMixedConjugation.local_higgs_transport
assert_compatible GUT.SMMixedConjugation.oppositeEquiv => Physics.SMMixedConjugation.oppositeEquiv
assert_compatible GUT.SMMixedConjugation.original_ql_iff => Physics.SMMixedConjugation.original_ql_iff
assert_compatible GUT.SMMixedConjugation.signed_charge_opposite => Physics.SMMixedConjugation.signed_charge_opposite
assert_compatible GUT.SMMixedConjugation.sourceEquiv => Physics.SMMixedConjugation.sourceEquiv
