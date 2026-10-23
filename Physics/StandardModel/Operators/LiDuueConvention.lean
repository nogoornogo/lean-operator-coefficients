import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueConvention
import Physics.StandardModel.Operators.DuueResidualCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiDuueConvention.alternatingSource => Physics.LiDuueConvention.alternatingSource,
  GUT.LiDuueConvention.alternatingSource.eq_1 => Physics.LiDuueConvention.alternatingSource.eq_1,
  GUT.LiDuueConvention.conjugate_alternating => Physics.LiDuueConvention.conjugate_alternating,
  GUT.LiDuueConvention.conjugate_symmetric => Physics.LiDuueConvention.conjugate_symmetric,
  GUT.LiDuueConvention.local_reconstruction => Physics.LiDuueConvention.local_reconstruction,
  GUT.LiDuueConvention.paperAlternating => Physics.LiDuueConvention.paperAlternating,
  GUT.LiDuueConvention.paperAlternating.eq_1 => Physics.LiDuueConvention.paperAlternating.eq_1,
  GUT.LiDuueConvention.paperSymmetric => Physics.LiDuueConvention.paperSymmetric,
  GUT.LiDuueConvention.paperSymmetric.eq_1 => Physics.LiDuueConvention.paperSymmetric.eq_1,
  GUT.LiDuueConvention.reorder_alternating => Physics.LiDuueConvention.reorder_alternating,
  GUT.LiDuueConvention.reorder_symmetric => Physics.LiDuueConvention.reorder_symmetric,
  GUT.LiDuueConvention.source_symmetries => Physics.LiDuueConvention.source_symmetries,
  GUT.LiDuueConvention.symmetricSource => Physics.LiDuueConvention.symmetricSource,
  GUT.LiDuueConvention.symmetricSource.eq_1 => Physics.LiDuueConvention.symmetricSource.eq_1
]

assert_compatible GUT.LiDuueConvention.alternatingSource => Physics.LiDuueConvention.alternatingSource
assert_compatible GUT.LiDuueConvention.alternatingSource.eq_1 => Physics.LiDuueConvention.alternatingSource.eq_1
assert_compatible GUT.LiDuueConvention.conjugate_alternating => Physics.LiDuueConvention.conjugate_alternating
assert_compatible GUT.LiDuueConvention.conjugate_symmetric => Physics.LiDuueConvention.conjugate_symmetric
assert_compatible GUT.LiDuueConvention.local_reconstruction => Physics.LiDuueConvention.local_reconstruction
assert_compatible GUT.LiDuueConvention.paperAlternating => Physics.LiDuueConvention.paperAlternating
assert_compatible GUT.LiDuueConvention.paperAlternating.eq_1 => Physics.LiDuueConvention.paperAlternating.eq_1
assert_compatible GUT.LiDuueConvention.paperSymmetric => Physics.LiDuueConvention.paperSymmetric
assert_compatible GUT.LiDuueConvention.paperSymmetric.eq_1 => Physics.LiDuueConvention.paperSymmetric.eq_1
assert_compatible GUT.LiDuueConvention.reorder_alternating => Physics.LiDuueConvention.reorder_alternating
assert_compatible GUT.LiDuueConvention.reorder_symmetric => Physics.LiDuueConvention.reorder_symmetric
assert_compatible GUT.LiDuueConvention.source_symmetries => Physics.LiDuueConvention.source_symmetries
assert_compatible GUT.LiDuueConvention.symmetricSource => Physics.LiDuueConvention.symmetricSource
assert_compatible GUT.LiDuueConvention.symmetricSource.eq_1 => Physics.LiDuueConvention.symmetricSource.eq_1
