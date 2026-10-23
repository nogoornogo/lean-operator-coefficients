import Physics.StandardModel.Operators.Support.Joint.SMSignedHiggsSupport
import Physics.StandardModel.Operators.SMQuarkAllHiggsSupport
import Physics.StandardModel.Operators.BnvLocalConjugation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMSignedHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvLocalConjugation.conjugate.eq_1 => Physics.BnvLocalConjugation.conjugate.eq_1,
  GUT.SMGaugeConjugation.conjugate.eq_1 => Physics.SMGaugeConjugation.conjugate.eq_1,
  GUT.SMSignedHiggsSupport.actionEquiv => Physics.SMSignedHiggsSupport.actionEquiv,
  GUT.SMSignedHiggsSupport.bosonEquiv => Physics.SMSignedHiggsSupport.bosonEquiv,
  GUT.SMSignedHiggsSupport.coefficientEquiv => Physics.SMSignedHiggsSupport.coefficientEquiv,
  GUT.SMSignedHiggsSupport.conjugate_lepton_charge => Physics.SMSignedHiggsSupport.conjugate_lepton_charge,
  GUT.SMSignedHiggsSupport.conjugate_lepton_local_iff => Physics.SMSignedHiggsSupport.conjugate_lepton_local_iff,
  GUT.SMSignedHiggsSupport.conjugate_lepton_ql_forbidden => Physics.SMSignedHiggsSupport.conjugate_lepton_ql_forbidden,
  GUT.SMSignedHiggsSupport.conjugate_lepton_ql_iff => Physics.SMSignedHiggsSupport.conjugate_lepton_ql_iff,
  GUT.SMSignedHiggsSupport.conjugate_quark_charge => Physics.SMSignedHiggsSupport.conjugate_quark_charge,
  GUT.SMSignedHiggsSupport.conjugate_quark_local_iff => Physics.SMSignedHiggsSupport.conjugate_quark_local_iff,
  GUT.SMSignedHiggsSupport.conjugate_quark_ql_forbidden => Physics.SMSignedHiggsSupport.conjugate_quark_ql_forbidden,
  GUT.SMSignedHiggsSupport.conjugate_quark_ql_iff => Physics.SMSignedHiggsSupport.conjugate_quark_ql_iff,
  GUT.SMSignedHiggsSupport.fieldEquiv => Physics.SMSignedHiggsSupport.fieldEquiv,
  GUT.SMSignedHiggsSupport.local_higgs_iff => Physics.SMSignedHiggsSupport.local_higgs_iff,
  GUT.SMSignedHiggsSupport.local_higgs_transport => Physics.SMSignedHiggsSupport.local_higgs_transport,
  GUT.SMSignedHiggsSupport.opposite_bound => Physics.SMSignedHiggsSupport.opposite_bound,
  GUT.SMSignedHiggsSupport.sourceEquiv => Physics.SMSignedHiggsSupport.sourceEquiv,
  GUT.SMSignedHiggsSupport.weakConjugate => Physics.SMSignedHiggsSupport.weakConjugate
]

assert_compatible GUT.BnvLocalConjugation.conjugate.eq_1 => Physics.BnvLocalConjugation.conjugate.eq_1
assert_compatible GUT.SMGaugeConjugation.conjugate.eq_1 => Physics.SMGaugeConjugation.conjugate.eq_1
assert_compatible GUT.SMSignedHiggsSupport.actionEquiv => Physics.SMSignedHiggsSupport.actionEquiv
assert_compatible GUT.SMSignedHiggsSupport.bosonEquiv => Physics.SMSignedHiggsSupport.bosonEquiv
assert_compatible GUT.SMSignedHiggsSupport.coefficientEquiv => Physics.SMSignedHiggsSupport.coefficientEquiv
assert_compatible GUT.SMSignedHiggsSupport.conjugate_lepton_charge => Physics.SMSignedHiggsSupport.conjugate_lepton_charge
assert_compatible GUT.SMSignedHiggsSupport.conjugate_lepton_local_iff => Physics.SMSignedHiggsSupport.conjugate_lepton_local_iff
assert_compatible GUT.SMSignedHiggsSupport.conjugate_lepton_ql_forbidden => Physics.SMSignedHiggsSupport.conjugate_lepton_ql_forbidden
assert_compatible GUT.SMSignedHiggsSupport.conjugate_lepton_ql_iff => Physics.SMSignedHiggsSupport.conjugate_lepton_ql_iff
assert_compatible GUT.SMSignedHiggsSupport.conjugate_quark_charge => Physics.SMSignedHiggsSupport.conjugate_quark_charge
assert_compatible GUT.SMSignedHiggsSupport.conjugate_quark_local_iff => Physics.SMSignedHiggsSupport.conjugate_quark_local_iff
assert_compatible GUT.SMSignedHiggsSupport.conjugate_quark_ql_forbidden => Physics.SMSignedHiggsSupport.conjugate_quark_ql_forbidden
assert_compatible GUT.SMSignedHiggsSupport.conjugate_quark_ql_iff => Physics.SMSignedHiggsSupport.conjugate_quark_ql_iff
assert_compatible GUT.SMSignedHiggsSupport.fieldEquiv => Physics.SMSignedHiggsSupport.fieldEquiv
assert_compatible GUT.SMSignedHiggsSupport.local_higgs_iff => Physics.SMSignedHiggsSupport.local_higgs_iff
assert_compatible GUT.SMSignedHiggsSupport.local_higgs_transport => Physics.SMSignedHiggsSupport.local_higgs_transport
assert_compatible GUT.SMSignedHiggsSupport.opposite_bound => Physics.SMSignedHiggsSupport.opposite_bound
assert_compatible GUT.SMSignedHiggsSupport.sourceEquiv => Physics.SMSignedHiggsSupport.sourceEquiv
assert_compatible GUT.SMSignedHiggsSupport.weakConjugate => Physics.SMSignedHiggsSupport.weakConjugate
