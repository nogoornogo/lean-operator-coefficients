import Physics.StandardModel.Operators.BaryonTwo.Coefficients.GradedSixQuarkComparison
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Math.RepresentationTheory.TypedMixedSeparatedHom
import Math.LinearAlgebra.LinearEquivComparison
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.GradedSixQuarkComparison instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.GradedSixQuarkComparison.Ordered => Physics.GradedSixQuarkComparison.Ordered,
  GUT.GradedSixQuarkComparison.Residual => Physics.GradedSixQuarkComparison.Residual,
  GUT.GradedSixQuarkComparison.boson => Physics.GradedSixQuarkComparison.boson,
  GUT.GradedSixQuarkComparison.comparison => Physics.GradedSixQuarkComparison.comparison,
  GUT.GradedSixQuarkComparison.emptyEquiv => Physics.GradedSixQuarkComparison.emptyEquiv,
  GUT.GradedSixQuarkComparison.emptyEquiv_symm_apply => Physics.GradedSixQuarkComparison.emptyEquiv_symm_apply,
  GUT.GradedSixQuarkComparison.equiv => Physics.GradedSixQuarkComparison.equiv,
  GUT.GradedSixQuarkComparison.equiv_def => Physics.GradedSixQuarkComparison.equiv_def,
  GUT.GradedSixQuarkComparison.extract_reconstruct => Physics.GradedSixQuarkComparison.extract_reconstruct,
  GUT.GradedSixQuarkComparison.extraction_commutes => Physics.GradedSixQuarkComparison.extraction_commutes,
  GUT.GradedSixQuarkComparison.fermion => Physics.GradedSixQuarkComparison.fermion,
  GUT.GradedSixQuarkComparison.field_apply => Physics.GradedSixQuarkComparison.field_apply,
  GUT.GradedSixQuarkComparison.flavor => Physics.GradedSixQuarkComparison.flavor,
  GUT.GradedSixQuarkComparison.forbidden_iff => Physics.GradedSixQuarkComparison.forbidden_iff,
  GUT.GradedSixQuarkComparison.fromOrdered => Physics.GradedSixQuarkComparison.fromOrdered,
  GUT.GradedSixQuarkComparison.localQuark => Physics.GradedSixQuarkComparison.localQuark,
  GUT.GradedSixQuarkComparison.localQuark.eq_1 => Physics.GradedSixQuarkComparison.localQuark.eq_1,
  GUT.GradedSixQuarkComparison.nonzero_iff => Physics.GradedSixQuarkComparison.nonzero_iff,
  GUT.GradedSixQuarkComparison.oneGenerationEquiv => Physics.GradedSixQuarkComparison.oneGenerationEquiv,
  GUT.GradedSixQuarkComparison.orderedEquiv => Physics.GradedSixQuarkComparison.orderedEquiv,
  GUT.GradedSixQuarkComparison.pattern => Physics.GradedSixQuarkComparison.pattern,
  GUT.GradedSixQuarkComparison.reconstruct_extract => Physics.GradedSixQuarkComparison.reconstruct_extract,
  GUT.GradedSixQuarkComparison.reconstruction_commutes => Physics.GradedSixQuarkComparison.reconstruction_commutes,
  GUT.GradedSixQuarkComparison.scalarFlavor => Physics.GradedSixQuarkComparison.scalarFlavor,
  GUT.GradedSixQuarkComparison.scalarLocal => Physics.GradedSixQuarkComparison.scalarLocal,
  GUT.GradedSixQuarkComparison.scalars => Physics.GradedSixQuarkComparison.scalars,
  GUT.GradedSixQuarkComparison.toOrdered => Physics.GradedSixQuarkComparison.toOrdered
]

assert_compatible GUT.GradedSixQuarkComparison.Ordered => Physics.GradedSixQuarkComparison.Ordered
assert_compatible GUT.GradedSixQuarkComparison.Residual => Physics.GradedSixQuarkComparison.Residual
assert_compatible GUT.GradedSixQuarkComparison.boson => Physics.GradedSixQuarkComparison.boson
assert_compatible GUT.GradedSixQuarkComparison.comparison => Physics.GradedSixQuarkComparison.comparison
assert_compatible GUT.GradedSixQuarkComparison.emptyEquiv => Physics.GradedSixQuarkComparison.emptyEquiv
assert_compatible GUT.GradedSixQuarkComparison.emptyEquiv_symm_apply => Physics.GradedSixQuarkComparison.emptyEquiv_symm_apply
assert_compatible GUT.GradedSixQuarkComparison.equiv => Physics.GradedSixQuarkComparison.equiv
assert_compatible GUT.GradedSixQuarkComparison.equiv_def => Physics.GradedSixQuarkComparison.equiv_def
assert_compatible GUT.GradedSixQuarkComparison.extract_reconstruct => Physics.GradedSixQuarkComparison.extract_reconstruct
assert_compatible GUT.GradedSixQuarkComparison.extraction_commutes => Physics.GradedSixQuarkComparison.extraction_commutes
assert_compatible GUT.GradedSixQuarkComparison.fermion => Physics.GradedSixQuarkComparison.fermion
assert_compatible GUT.GradedSixQuarkComparison.field_apply => Physics.GradedSixQuarkComparison.field_apply
assert_compatible GUT.GradedSixQuarkComparison.flavor => Physics.GradedSixQuarkComparison.flavor
assert_compatible GUT.GradedSixQuarkComparison.forbidden_iff => Physics.GradedSixQuarkComparison.forbidden_iff
assert_compatible GUT.GradedSixQuarkComparison.fromOrdered => Physics.GradedSixQuarkComparison.fromOrdered
assert_compatible GUT.GradedSixQuarkComparison.localQuark => Physics.GradedSixQuarkComparison.localQuark
assert_compatible GUT.GradedSixQuarkComparison.localQuark.eq_1 => Physics.GradedSixQuarkComparison.localQuark.eq_1
assert_compatible GUT.GradedSixQuarkComparison.nonzero_iff => Physics.GradedSixQuarkComparison.nonzero_iff
assert_compatible GUT.GradedSixQuarkComparison.oneGenerationEquiv => Physics.GradedSixQuarkComparison.oneGenerationEquiv
assert_compatible GUT.GradedSixQuarkComparison.orderedEquiv => Physics.GradedSixQuarkComparison.orderedEquiv
assert_compatible GUT.GradedSixQuarkComparison.pattern => Physics.GradedSixQuarkComparison.pattern
assert_compatible GUT.GradedSixQuarkComparison.reconstruct_extract => Physics.GradedSixQuarkComparison.reconstruct_extract
assert_compatible GUT.GradedSixQuarkComparison.reconstruction_commutes => Physics.GradedSixQuarkComparison.reconstruction_commutes
assert_compatible GUT.GradedSixQuarkComparison.scalarFlavor => Physics.GradedSixQuarkComparison.scalarFlavor
assert_compatible GUT.GradedSixQuarkComparison.scalarLocal => Physics.GradedSixQuarkComparison.scalarLocal
assert_compatible GUT.GradedSixQuarkComparison.scalars => Physics.GradedSixQuarkComparison.scalars
assert_compatible GUT.GradedSixQuarkComparison.toOrdered => Physics.GradedSixQuarkComparison.toOrdered
