import Math.LieGroups.SpecialUnitary.Block
import GUT.SU6.Embeddings.StandardSU5Inclusion

open Math

/-! The general block inclusion at rank six is the existing SU(6) map,
not merely a conjugate or character-level replacement. -/

set_option autoImplicit false

namespace GUT.SU6.StandardSUNCompatibility

noncomputable section

set_option maxRecDepth 2000 in
theorem inclusion_eq : SUN.Block.inclusion 5 1 = StandardSU5Inclusion.inclusion := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply congrArg (Matrix.reindex (SUN.Block.indexEquiv 5 1) (SUN.Block.indexEquiv 5 1))
  change Matrix.fromBlocks A.val 0 0 1 =
    Matrix.fromBlocks A.val 0 0 (StandardU5Group.singletBlock (StandardSU5Inclusion.toU5 A))
  have hd : Matrix.det (StandardSU5Inclusion.toU5 A).val = 1 := A.property.2
  simp only [StandardU5Group.singletBlock, hd, star_one, Matrix.diagonal_one]

theorem torus_eq (x : PhysicalSMTorusTarget.Group) :
    SUN.Block.inclusion 5 1 (SU5.MaximalTorus.hom (SU5TorusCompatibility.torusCover x)) =
      PhysicalSMTorusTarget.embedding (-2) 3 x := by
  rw [inclusion_eq, StandardSU5Inclusion.inclusion_torus]

end

end GUT.SU6.StandardSUNCompatibility
