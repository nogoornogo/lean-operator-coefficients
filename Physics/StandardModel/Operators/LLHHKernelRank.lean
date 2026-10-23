import Physics.StandardModel.Operators.Weinberg.LLHHKernelRank
import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMFullLocalKernel
import Physics.StandardModel.Operators.LiWeinbergCertificate
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.LLHHKernelRank instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LLHHKernelRank.a => Physics.LLHHKernelRank.a,
  GUT.LLHHKernelRank.bosonEquiv => Physics.LLHHKernelRank.bosonEquiv,
  GUT.LLHHKernelRank.carrierBasis => Physics.LLHHKernelRank.carrierBasis,
  GUT.LLHHKernelRank.carrier_dimension => Physics.LLHHKernelRank.carrier_dimension,
  GUT.LLHHKernelRank.coefficientBasis => Physics.LLHHKernelRank.coefficientBasis,
  GUT.LLHHKernelRank.coefficientEquiv => Physics.LLHHKernelRank.coefficientEquiv,
  GUT.LLHHKernelRank.coordinates => Physics.LLHHKernelRank.coordinates,
  GUT.LLHHKernelRank.explicit_rank => Physics.LLHHKernelRank.explicit_rank,
  GUT.LLHHKernelRank.extract_reconstruct => Physics.LLHHKernelRank.extract_reconstruct,
  GUT.LLHHKernelRank.flavor => Physics.LLHHKernelRank.flavor,
  GUT.LLHHKernelRank.fullEquiv => Physics.LLHHKernelRank.fullEquiv,
  GUT.LLHHKernelRank.inclusion_surjective => Physics.LLHHKernelRank.inclusion_surjective,
  GUT.LLHHKernelRank.instAddCommGroupLeptonForallFinOfNatNatComplex => Physics.LLHHKernelRank.instAddCommGroupLeptonForallFinOfNatNatComplex,
  GUT.LLHHKernelRank.instAddCommGroupTensorProductComplexWeakSpace => Physics.LLHHKernelRank.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.LLHHKernelRank.kernelCoordinates => Physics.LLHHKernelRank.kernelCoordinates,
  GUT.LLHHKernelRank.kernel_dimension => Physics.LLHHKernelRank.kernel_dimension,
  GUT.LLHHKernelRank.leptonBasis => Physics.LLHHKernelRank.leptonBasis,
  GUT.LLHHKernelRank.localEquiv => Physics.LLHHKernelRank.localEquiv,
  GUT.LLHHKernelRank.pattern => Physics.LLHHKernelRank.pattern,
  GUT.LLHHKernelRank.rank => Physics.LLHHKernelRank.rank,
  GUT.LLHHKernelRank.rank_preserved => Physics.LLHHKernelRank.rank_preserved,
  GUT.LLHHKernelRank.reconstruct_extract => Physics.LLHHKernelRank.reconstruct_extract,
  GUT.LLHHKernelRank.residualEquiv => Physics.LLHHKernelRank.residualEquiv,
  GUT.LLHHKernelRank.sourceEquiv => Physics.LLHHKernelRank.sourceEquiv
]

assert_compatible GUT.LLHHKernelRank.a => Physics.LLHHKernelRank.a
assert_compatible GUT.LLHHKernelRank.bosonEquiv => Physics.LLHHKernelRank.bosonEquiv
assert_compatible GUT.LLHHKernelRank.carrierBasis => Physics.LLHHKernelRank.carrierBasis
assert_compatible GUT.LLHHKernelRank.carrier_dimension => Physics.LLHHKernelRank.carrier_dimension
assert_compatible GUT.LLHHKernelRank.coefficientBasis => Physics.LLHHKernelRank.coefficientBasis
assert_compatible GUT.LLHHKernelRank.coefficientEquiv => Physics.LLHHKernelRank.coefficientEquiv
assert_compatible GUT.LLHHKernelRank.coordinates => Physics.LLHHKernelRank.coordinates
assert_compatible GUT.LLHHKernelRank.explicit_rank => Physics.LLHHKernelRank.explicit_rank
assert_compatible GUT.LLHHKernelRank.extract_reconstruct => Physics.LLHHKernelRank.extract_reconstruct
assert_compatible GUT.LLHHKernelRank.flavor => Physics.LLHHKernelRank.flavor
assert_compatible GUT.LLHHKernelRank.fullEquiv => Physics.LLHHKernelRank.fullEquiv
assert_compatible GUT.LLHHKernelRank.inclusion_surjective => Physics.LLHHKernelRank.inclusion_surjective
assert_compatible GUT.LLHHKernelRank.instAddCommGroupLeptonForallFinOfNatNatComplex => Physics.LLHHKernelRank.instAddCommGroupLeptonForallFinOfNatNatComplex
assert_compatible GUT.LLHHKernelRank.instAddCommGroupTensorProductComplexWeakSpace => Physics.LLHHKernelRank.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.LLHHKernelRank.kernelCoordinates => Physics.LLHHKernelRank.kernelCoordinates
assert_compatible GUT.LLHHKernelRank.kernel_dimension => Physics.LLHHKernelRank.kernel_dimension
assert_compatible GUT.LLHHKernelRank.leptonBasis => Physics.LLHHKernelRank.leptonBasis
assert_compatible GUT.LLHHKernelRank.localEquiv => Physics.LLHHKernelRank.localEquiv
assert_compatible GUT.LLHHKernelRank.pattern => Physics.LLHHKernelRank.pattern
assert_compatible GUT.LLHHKernelRank.rank => Physics.LLHHKernelRank.rank
assert_compatible GUT.LLHHKernelRank.rank_preserved => Physics.LLHHKernelRank.rank_preserved
assert_compatible GUT.LLHHKernelRank.reconstruct_extract => Physics.LLHHKernelRank.reconstruct_extract
assert_compatible GUT.LLHHKernelRank.residualEquiv => Physics.LLHHKernelRank.residualEquiv
assert_compatible GUT.LLHHKernelRank.sourceEquiv => Physics.LLHHKernelRank.sourceEquiv
