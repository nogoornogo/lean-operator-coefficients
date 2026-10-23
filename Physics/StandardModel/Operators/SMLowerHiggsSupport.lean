import Physics.StandardModel.Operators.Support.Lepton.SMLowerHiggsSupport
import Physics.StandardModel.Operators.SMLowerGenerationSupport
import Physics.StandardModel.Operators.SMParityKernelRank
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLowerHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLowerHiggsSupport.LocalHiggs => Physics.SMLowerHiggsSupport.LocalHiggs,
  GUT.SMLowerHiggsSupport.lepton_all_local_iff => Physics.SMLowerHiggsSupport.lepton_all_local_iff,
  GUT.SMLowerHiggsSupport.lepton_local_iff => Physics.SMLowerHiggsSupport.lepton_local_iff,
  GUT.SMLowerHiggsSupport.lepton_original_iff => Physics.SMLowerHiggsSupport.lepton_original_iff,
  GUT.SMLowerHiggsSupport.lepton_positive_local_iff => Physics.SMLowerHiggsSupport.lepton_positive_local_iff,
  GUT.SMLowerHiggsSupport.lepton_ql_all_forbidden => Physics.SMLowerHiggsSupport.lepton_ql_all_forbidden,
  GUT.SMLowerHiggsSupport.lepton_ql_all_iff => Physics.SMLowerHiggsSupport.lepton_ql_all_iff,
  GUT.SMLowerHiggsSupport.lepton_ql_iff => Physics.SMLowerHiggsSupport.lepton_ql_iff,
  GUT.SMLowerHiggsSupport.lepton_residual_charge => Physics.SMLowerHiggsSupport.lepton_residual_charge,
  GUT.SMLowerHiggsSupport.localActionEquiv => Physics.SMLowerHiggsSupport.localActionEquiv,
  GUT.SMLowerHiggsSupport.local_surjective => Physics.SMLowerHiggsSupport.local_surjective,
  GUT.SMLowerHiggsSupport.qlLocalEquiv => Physics.SMLowerHiggsSupport.qlLocalEquiv,
  GUT.SMLowerHiggsSupport.ql_original_iff => Physics.SMLowerHiggsSupport.ql_original_iff,
  GUT.SMLowerHiggsSupport.quark_local_iff => Physics.SMLowerHiggsSupport.quark_local_iff,
  GUT.SMLowerHiggsSupport.quark_lower_local_iff => Physics.SMLowerHiggsSupport.quark_lower_local_iff,
  GUT.SMLowerHiggsSupport.quark_original_iff => Physics.SMLowerHiggsSupport.quark_original_iff,
  GUT.SMLowerHiggsSupport.quark_positive_lower_local_iff => Physics.SMLowerHiggsSupport.quark_positive_lower_local_iff,
  GUT.SMLowerHiggsSupport.quark_ql_iff => Physics.SMLowerHiggsSupport.quark_ql_iff,
  GUT.SMLowerHiggsSupport.quark_ql_lower_forbidden => Physics.SMLowerHiggsSupport.quark_ql_lower_forbidden,
  GUT.SMLowerHiggsSupport.quark_ql_lower_iff => Physics.SMLowerHiggsSupport.quark_ql_lower_iff,
  GUT.SMLowerHiggsSupport.quark_residual_charge => Physics.SMLowerHiggsSupport.quark_residual_charge,
  GUT.SMLowerHiggsSupport.trivialFlavor => Physics.SMLowerHiggsSupport.trivialFlavor,
  GUT.SMLowerHiggsSupport.trivialTestEquiv => Physics.SMLowerHiggsSupport.trivialTestEquiv,
  GUT.SMLowerHiggsSupport.trivial_original_iff => Physics.SMLowerHiggsSupport.trivial_original_iff,
  GUT.SMLowerHiggsSupport.vacuum_local_iff => Physics.SMLowerHiggsSupport.vacuum_local_iff
]

assert_compatible GUT.SMLowerHiggsSupport.LocalHiggs => Physics.SMLowerHiggsSupport.LocalHiggs
assert_compatible GUT.SMLowerHiggsSupport.lepton_all_local_iff => Physics.SMLowerHiggsSupport.lepton_all_local_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_local_iff => Physics.SMLowerHiggsSupport.lepton_local_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_original_iff => Physics.SMLowerHiggsSupport.lepton_original_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_positive_local_iff => Physics.SMLowerHiggsSupport.lepton_positive_local_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_ql_all_forbidden => Physics.SMLowerHiggsSupport.lepton_ql_all_forbidden
assert_compatible GUT.SMLowerHiggsSupport.lepton_ql_all_iff => Physics.SMLowerHiggsSupport.lepton_ql_all_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_ql_iff => Physics.SMLowerHiggsSupport.lepton_ql_iff
assert_compatible GUT.SMLowerHiggsSupport.lepton_residual_charge => Physics.SMLowerHiggsSupport.lepton_residual_charge
assert_compatible GUT.SMLowerHiggsSupport.localActionEquiv => Physics.SMLowerHiggsSupport.localActionEquiv
assert_compatible GUT.SMLowerHiggsSupport.local_surjective => Physics.SMLowerHiggsSupport.local_surjective
assert_compatible GUT.SMLowerHiggsSupport.qlLocalEquiv => Physics.SMLowerHiggsSupport.qlLocalEquiv
assert_compatible GUT.SMLowerHiggsSupport.ql_original_iff => Physics.SMLowerHiggsSupport.ql_original_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_local_iff => Physics.SMLowerHiggsSupport.quark_local_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_lower_local_iff => Physics.SMLowerHiggsSupport.quark_lower_local_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_original_iff => Physics.SMLowerHiggsSupport.quark_original_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_positive_lower_local_iff => Physics.SMLowerHiggsSupport.quark_positive_lower_local_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_ql_iff => Physics.SMLowerHiggsSupport.quark_ql_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_ql_lower_forbidden => Physics.SMLowerHiggsSupport.quark_ql_lower_forbidden
assert_compatible GUT.SMLowerHiggsSupport.quark_ql_lower_iff => Physics.SMLowerHiggsSupport.quark_ql_lower_iff
assert_compatible GUT.SMLowerHiggsSupport.quark_residual_charge => Physics.SMLowerHiggsSupport.quark_residual_charge
assert_compatible GUT.SMLowerHiggsSupport.trivialFlavor => Physics.SMLowerHiggsSupport.trivialFlavor
assert_compatible GUT.SMLowerHiggsSupport.trivialTestEquiv => Physics.SMLowerHiggsSupport.trivialTestEquiv
assert_compatible GUT.SMLowerHiggsSupport.trivial_original_iff => Physics.SMLowerHiggsSupport.trivial_original_iff
assert_compatible GUT.SMLowerHiggsSupport.vacuum_local_iff => Physics.SMLowerHiggsSupport.vacuum_local_iff
