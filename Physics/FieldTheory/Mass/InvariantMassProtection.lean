import Physics.FieldTheory.Mass.Algebra.InvariantMassProtection
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.InvariantMassProtection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantMassProtection.Extends => Physics.InvariantMassProtection.Extends,
  GUT.InvariantMassProtection.Preserves => Physics.InvariantMassProtection.Preserves,
  GUT.InvariantMassProtection.UniversallyProtected => Physics.InvariantMassProtection.UniversallyProtected,
  GUT.InvariantMassProtection.UniversallyProtected.eq_1 => Physics.InvariantMassProtection.UniversallyProtected.eq_1,
  GUT.InvariantMassProtection.block => Physics.InvariantMassProtection.block,
  GUT.InvariantMassProtection.block_apply => Physics.InvariantMassProtection.block_apply,
  GUT.InvariantMassProtection.block_extends => Physics.InvariantMassProtection.block_extends,
  GUT.InvariantMassProtection.cross => Physics.InvariantMassProtection.cross,
  GUT.InvariantMassProtection.cross_block => Physics.InvariantMassProtection.cross_block,
  GUT.InvariantMassProtection.exists_lifting_iff_common => Physics.InvariantMassProtection.exists_lifting_iff_common,
  GUT.InvariantMassProtection.family_iff => Physics.InvariantMassProtection.family_iff,
  GUT.InvariantMassProtection.lightInclusion => Physics.InvariantMassProtection.lightInclusion,
  GUT.InvariantMassProtection.light_semisimple => Physics.InvariantMassProtection.light_semisimple,
  GUT.InvariantMassProtection.preserves_iff => Physics.InvariantMassProtection.preserves_iff,
  GUT.InvariantMassProtection.radicalMap => Physics.InvariantMassProtection.radicalMap,
  GUT.InvariantMassProtection.radicalMap_injective => Physics.InvariantMassProtection.radicalMap_injective,
  GUT.InvariantMassProtection.universal_iff_hom_zero => Physics.InvariantMassProtection.universal_iff_hom_zero,
  GUT.InvariantMassProtection.universal_iff_hom_zero_of_retraction => Physics.InvariantMassProtection.universal_iff_hom_zero_of_retraction,
  GUT.InvariantMassProtection.universal_iff_no_common => Physics.InvariantMassProtection.universal_iff_no_common,
  GUT.InvariantMassProtection.universal_iff_restriction => Physics.InvariantMassProtection.universal_iff_restriction,
  GUT.InvariantMassProtection.universal_of_hom_zero => Physics.InvariantMassProtection.universal_of_hom_zero
]

assert_compatible GUT.InvariantMassProtection.Extends => Physics.InvariantMassProtection.Extends
assert_compatible GUT.InvariantMassProtection.Preserves => Physics.InvariantMassProtection.Preserves
assert_compatible GUT.InvariantMassProtection.UniversallyProtected => Physics.InvariantMassProtection.UniversallyProtected
assert_compatible GUT.InvariantMassProtection.UniversallyProtected.eq_1 => Physics.InvariantMassProtection.UniversallyProtected.eq_1
assert_compatible GUT.InvariantMassProtection.block => Physics.InvariantMassProtection.block
assert_compatible GUT.InvariantMassProtection.block_apply => Physics.InvariantMassProtection.block_apply
assert_compatible GUT.InvariantMassProtection.block_extends => Physics.InvariantMassProtection.block_extends
assert_compatible GUT.InvariantMassProtection.cross => Physics.InvariantMassProtection.cross
assert_compatible GUT.InvariantMassProtection.cross_block => Physics.InvariantMassProtection.cross_block
assert_compatible GUT.InvariantMassProtection.exists_lifting_iff_common => Physics.InvariantMassProtection.exists_lifting_iff_common
assert_compatible GUT.InvariantMassProtection.family_iff => Physics.InvariantMassProtection.family_iff
assert_compatible GUT.InvariantMassProtection.lightInclusion => Physics.InvariantMassProtection.lightInclusion
assert_compatible GUT.InvariantMassProtection.light_semisimple => Physics.InvariantMassProtection.light_semisimple
assert_compatible GUT.InvariantMassProtection.preserves_iff => Physics.InvariantMassProtection.preserves_iff
assert_compatible GUT.InvariantMassProtection.radicalMap => Physics.InvariantMassProtection.radicalMap
assert_compatible GUT.InvariantMassProtection.radicalMap_injective => Physics.InvariantMassProtection.radicalMap_injective
assert_compatible GUT.InvariantMassProtection.universal_iff_hom_zero => Physics.InvariantMassProtection.universal_iff_hom_zero
assert_compatible GUT.InvariantMassProtection.universal_iff_hom_zero_of_retraction => Physics.InvariantMassProtection.universal_iff_hom_zero_of_retraction
assert_compatible GUT.InvariantMassProtection.universal_iff_no_common => Physics.InvariantMassProtection.universal_iff_no_common
assert_compatible GUT.InvariantMassProtection.universal_iff_restriction => Physics.InvariantMassProtection.universal_iff_restriction
assert_compatible GUT.InvariantMassProtection.universal_of_hom_zero => Physics.InvariantMassProtection.universal_of_hom_zero
