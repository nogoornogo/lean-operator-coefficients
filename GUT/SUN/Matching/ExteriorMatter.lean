import Math.RepresentationTheory.ExteriorSquareBlock
import GUT.SU5.Matching.HeavyCurrents

open Math

/-! Actual defining and exterior-square SU(5+r) actions, with the retained
SU(5) embedded by a unitary determinant-one block inclusion. -/
set_option autoImplicit false
namespace GUT.SUN.ExteriorMatter

noncomputable section
open ExteriorSquareBlock
variable (r : ℕ)

abbrev Group := Matrix.specialUnitaryGroup (Fin (5+r)) ℂ
def fundamental : Representation ℂ (Group r) (Fin (5+r) → ℂ) where
  toFun g := Matrix.toLin' (g : Matrix (Fin (5+r)) (Fin (5+r)) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _
def matter := (fundamental r).exteriorPower 2

def rawHom : SU5.StandardModelEmbedding.TargetGroup →*
    Matrix (Fin 5 ⊕ Fin r) (Fin 5 ⊕ Fin r) ℂ where
  toFun g := Matrix.fromBlocks (g : Matrix (Fin 5) (Fin 5) ℂ) 0 0 1
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' g h := by simp [Matrix.fromBlocks_multiply]
def matrixHom : SU5.StandardModelEmbedding.TargetGroup →*
    Matrix (Fin (5+r)) (Fin (5+r)) ℂ :=
  (Matrix.reindexRingEquiv ℂ finSumFinEquiv).toMonoidHom.comp (rawHom r)

theorem matrixHom_unitary (g : SU5.StandardModelEmbedding.TargetGroup) :
    matrixHom r g ∈ Matrix.unitaryGroup (Fin (5+r)) ℂ := by
  have hg := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.prop)
  have h : rawHom r g * star (rawHom r g) = 1 := by
    simpa [rawHom, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply] using
      congrArg (fun X : Matrix (Fin 5) (Fin 5) ℂ =>
        Matrix.fromBlocks X (0 : Matrix (Fin 5) (Fin r) ℂ) 0
          (1 : Matrix (Fin r) (Fin r) ℂ)) hg
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (rawHom r g) *
    star (Matrix.reindex finSumFinEquiv finSumFinEquiv (rawHom r g)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ finSumFinEquiv) (rawHom r g) *
    (Matrix.reindexRingEquiv ℂ finSumFinEquiv) (star (rawHom r g)) = 1
  rw [← map_mul, h, map_one]

theorem matrixHom_det (g : SU5.StandardModelEmbedding.TargetGroup) :
    Matrix.det (matrixHom r g) = 1 := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv (rawHom r g)) = 1
  rw [Matrix.det_reindex_self]
  simpa [rawHom, Matrix.det_fromBlocks_zero₂₁] using g.prop.2

def inclusion : SU5.StandardModelEmbedding.TargetGroup →* Group r where
  toFun g := ⟨matrixHom r g, matrixHom_unitary r g, matrixHom_det r g⟩
  map_one' := Subtype.ext (map_one (matrixHom r))
  map_mul' g h := Subtype.ext (map_mul (matrixHom r) g h)

theorem cut_matrixHom (g : SU5.StandardModelEmbedding.TargetGroup) :
    cut r (matrixHom r g) = (g : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  simp [cut, matrixHom, rawHom, Matrix.reindex_apply]

theorem inclusion_injective : Function.Injective (inclusion r) := by
  intro g h he
  have he' := congrArg (fun z : Group r => cut r (z : Matrix (Fin (5+r)) (Fin (5+r)) ℂ)) he
  change cut r (matrixHom r g) = cut r (matrixHom r h) at he'
  apply Subtype.ext
  simpa only [cut_matrixHom] using he'

theorem fundamental_include (g : SU5.StandardModelEmbedding.TargetGroup) (x : Fin 5 → ℂ) :
    fundamental r (inclusion r g) (includeFive r x) =
      includeFive r (SU5.Matter.fundamental g x) := by
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [fundamental, inclusion, matrixHom, rawHom, Matrix.reindex_apply,
      includeFive, SU5.Matter.fundamental, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct]
  · simp [fundamental, inclusion, matrixHom, rawHom, Matrix.reindex_apply,
      includeFive, SU5.Matter.fundamental, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct]

theorem matter_embed (g : SU5.StandardModelEmbedding.TargetGroup) (x : SU5.Matter.Ten) :
    matter r (inclusion r g) (embed r x) = embed r (SU5.Matter.ten g x) := by
  have h : (fundamental r (inclusion r g)).comp (includeFive r) =
      (includeFive r).comp (SU5.Matter.fundamental g) :=
    LinearMap.ext (fundamental_include r g)
  have he := congrArg (exteriorPower.map (R := ℂ) 2) h
  simp only [exteriorPower.map_comp] at he
  exact DFunLike.congr_fun he x

theorem retained_branch (x : SU5.Matter.Ten) :
    SU5.ExteriorSquareBranching.branch (project r (embed r x)) =
      SU5.ExteriorSquareBranching.branch x := by
  have h := DFunLike.congr_fun (project_embed r) x
  exact congrArg SU5.ExteriorSquareBranching.branch h

theorem quark_covariant (g : StandardSMGaugeTensor.GaugeGroup) (q : StandardSMGaugeTensor.Quark) :
    matter r (inclusion r (SU5.StandardModelEmbedding.hom g))
      (embed r (SU5.HeavyCurrents.quarkEmbed q)) =
      embed r (SU5.HeavyCurrents.quarkEmbed (StandardSMGaugeTensor.quark g q)) := by
  rw [matter_embed]
  congr 1
  apply SU5.ExteriorSquareBranching.branch_bijective.1
  have h := Representation.IntertwiningMap.isIntertwining _ _
    SU5.ExteriorSquareBranching.branchIntertwiner g (SU5.HeavyCurrents.quarkEmbed q)
  change SU5.ExteriorSquareBranching.branch
    (SU5.Matter.ten (SU5.StandardModelEmbedding.hom g) (SU5.HeavyCurrents.quarkEmbed q)) =
    SU5.ExteriorSquareBranching.blocksRho g
    (SU5.ExteriorSquareBranching.branch (SU5.HeavyCurrents.quarkEmbed q)) at h
  rw [h, SU5.HeavyCurrents.branch_quarkEmbed, SU5.HeavyCurrents.branch_quarkEmbed]
  simp [SU5.ExteriorSquareBranching.blocksRho, Representation.prod]

theorem actual_action (g : Group r) :
    matter r g = exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin (5+r)) (Fin (5+r)) ℂ)) := rfl

end
end GUT.SUN.ExteriorMatter
