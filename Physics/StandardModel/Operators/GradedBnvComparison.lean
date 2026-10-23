import Physics.StandardModel.Operators.BaryonOne.Inputs.GradedBnvComparison
import Physics.StandardModel.Operators.BnvSevenCompleteness
import Math.RepresentationTheory.GradedMixedCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.GradedBnvComparison instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.GradedBnvComparison.Residual => Physics.GradedBnvComparison.Residual,
  GUT.GradedBnvComparison.ResidualProduct => Physics.GradedBnvComparison.ResidualProduct,
  GUT.GradedBnvComparison.allowed => Physics.GradedBnvComparison.allowed,
  GUT.GradedBnvComparison.allowed.eq_1 => Physics.GradedBnvComparison.allowed.eq_1,
  GUT.GradedBnvComparison.boson => Physics.GradedBnvComparison.boson,
  GUT.GradedBnvComparison.boson.eq_1 => Physics.GradedBnvComparison.boson.eq_1,
  GUT.GradedBnvComparison.boson_eq => Physics.GradedBnvComparison.boson_eq,
  GUT.GradedBnvComparison.boundedSevenEquiv => Physics.GradedBnvComparison.boundedSevenEquiv,
  GUT.GradedBnvComparison.comparison => Physics.GradedBnvComparison.comparison,
  GUT.GradedBnvComparison.extract_reconstruct => Physics.GradedBnvComparison.extract_reconstruct,
  GUT.GradedBnvComparison.extraction_commutes => Physics.GradedBnvComparison.extraction_commutes,
  GUT.GradedBnvComparison.fermion => Physics.GradedBnvComparison.fermion,
  GUT.GradedBnvComparison.fermion.eq_1 => Physics.GradedBnvComparison.fermion.eq_1,
  GUT.GradedBnvComparison.fermion_eq => Physics.GradedBnvComparison.fermion_eq,
  GUT.GradedBnvComparison.forbidden_iff => Physics.GradedBnvComparison.forbidden_iff,
  GUT.GradedBnvComparison.nonzero_iff => Physics.GradedBnvComparison.nonzero_iff,
  GUT.GradedBnvComparison.perDegreeEquiv => Physics.GradedBnvComparison.perDegreeEquiv,
  GUT.GradedBnvComparison.reconstruct_extract => Physics.GradedBnvComparison.reconstruct_extract,
  GUT.GradedBnvComparison.reconstruction_commutes => Physics.GradedBnvComparison.reconstruction_commutes,
  GUT.GradedBnvComparison.scalarLocal => Physics.GradedBnvComparison.scalarLocal,
  GUT.GradedBnvComparison.scalarLocal.eq_1 => Physics.GradedBnvComparison.scalarLocal.eq_1,
  GUT.GradedBnvComparison.sevenComparison => Physics.GradedBnvComparison.sevenComparison,
  GUT.GradedBnvComparison.sixComparison => Physics.GradedBnvComparison.sixComparison,
  GUT.GradedBnvComparison.stable => Physics.GradedBnvComparison.stable,
  GUT.GradedBnvComparison.supportEquiv => Physics.GradedBnvComparison.supportEquiv,
  GUT.GradedBnvComparison.supportPresentation => Physics.GradedBnvComparison.supportPresentation
]

assert_compatible GUT.GradedBnvComparison.Residual => Physics.GradedBnvComparison.Residual
assert_compatible GUT.GradedBnvComparison.ResidualProduct => Physics.GradedBnvComparison.ResidualProduct
assert_compatible GUT.GradedBnvComparison.allowed => Physics.GradedBnvComparison.allowed
assert_compatible GUT.GradedBnvComparison.allowed.eq_1 => Physics.GradedBnvComparison.allowed.eq_1
assert_compatible GUT.GradedBnvComparison.boson => Physics.GradedBnvComparison.boson
assert_compatible GUT.GradedBnvComparison.boson.eq_1 => Physics.GradedBnvComparison.boson.eq_1
assert_compatible GUT.GradedBnvComparison.boson_eq => Physics.GradedBnvComparison.boson_eq
assert_compatible GUT.GradedBnvComparison.boundedSevenEquiv => Physics.GradedBnvComparison.boundedSevenEquiv
assert_compatible GUT.GradedBnvComparison.comparison => Physics.GradedBnvComparison.comparison
assert_compatible GUT.GradedBnvComparison.extract_reconstruct => Physics.GradedBnvComparison.extract_reconstruct
assert_compatible GUT.GradedBnvComparison.extraction_commutes => Physics.GradedBnvComparison.extraction_commutes
assert_compatible GUT.GradedBnvComparison.fermion => Physics.GradedBnvComparison.fermion
assert_compatible GUT.GradedBnvComparison.fermion.eq_1 => Physics.GradedBnvComparison.fermion.eq_1
assert_compatible GUT.GradedBnvComparison.fermion_eq => Physics.GradedBnvComparison.fermion_eq
assert_compatible GUT.GradedBnvComparison.forbidden_iff => Physics.GradedBnvComparison.forbidden_iff
assert_compatible GUT.GradedBnvComparison.nonzero_iff => Physics.GradedBnvComparison.nonzero_iff
assert_compatible GUT.GradedBnvComparison.perDegreeEquiv => Physics.GradedBnvComparison.perDegreeEquiv
assert_compatible GUT.GradedBnvComparison.reconstruct_extract => Physics.GradedBnvComparison.reconstruct_extract
assert_compatible GUT.GradedBnvComparison.reconstruction_commutes => Physics.GradedBnvComparison.reconstruction_commutes
assert_compatible GUT.GradedBnvComparison.scalarLocal => Physics.GradedBnvComparison.scalarLocal
assert_compatible GUT.GradedBnvComparison.scalarLocal.eq_1 => Physics.GradedBnvComparison.scalarLocal.eq_1
assert_compatible GUT.GradedBnvComparison.sevenComparison => Physics.GradedBnvComparison.sevenComparison
assert_compatible GUT.GradedBnvComparison.sixComparison => Physics.GradedBnvComparison.sixComparison
assert_compatible GUT.GradedBnvComparison.stable => Physics.GradedBnvComparison.stable
assert_compatible GUT.GradedBnvComparison.supportEquiv => Physics.GradedBnvComparison.supportEquiv
assert_compatible GUT.GradedBnvComparison.supportPresentation => Physics.GradedBnvComparison.supportPresentation
