import GUT.SU6.SelectionRules.FlippedBranch.ColorNeutralBranch
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The concrete color-neutral Standard Model subgroup

The global group naturally visible in the color-neutral branch is
`SU(3) x U(2)`.  This file constructs its block embedding

`(A,B) |-> diag(A,B,det(B)^-1)`

into `SU(6)`.  It also proves that every point of the actual color-neutral
diagonal torus lifts through this embedding.  The defining block weights are
therefore `(0,0,0,1,1,-2)` along the central circle of `U(2)`.
-/

namespace GUT
namespace ColorNeutralSMGroup

noncomputable section

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev U2 := Matrix.unitaryGroup (Fin 2) ℂ
abbrev Group := SU3 × U2
abbrev BlockIndex := Fin 3 ⊕ (Fin 2 ⊕ Fin 1)

def blockIndexEquiv : BlockIndex ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) (@finSumFinEquiv 2 1)).trans
    (@finSumFinEquiv 3 3)

def singletBlock (B : U2) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => star (Matrix.det (B : Matrix (Fin 2) (Fin 2) ℂ))

theorem star_det_eq_inv_det (B : U2) :
    star (Matrix.det (B : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Matrix.det (B : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ := by
  have hunit := Matrix.det_of_mem_unitary B.prop
  have hne : Matrix.det (B : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit B).ne_zero
  exact (mul_eq_one_iff_eq_inv₀ hne).mp hunit.1

def rawEmbeddingMatrix (g : Group) : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (g.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
    (Matrix.fromBlocks (g.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      (singletBlock g.2))

theorem rawEmbeddingMatrix_one : rawEmbeddingMatrix 1 = 1 := by
  simp [rawEmbeddingMatrix, singletBlock, Matrix.fromBlocks_one]

theorem rawEmbeddingMatrix_mul (g h : Group) :
    rawEmbeddingMatrix (g * h) =
      rawEmbeddingMatrix g * rawEmbeddingMatrix h := by
  simp [rawEmbeddingMatrix, singletBlock, Matrix.fromBlocks_multiply,
    Matrix.det_mul]

theorem singletBlock_mem_unitary (B : U2) :
    singletBlock B ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hdet := Matrix.det_of_mem_unitary B.prop
  ext i j
  fin_cases i
  fin_cases j
  simpa [singletBlock, Matrix.mul_apply] using hdet.1

theorem rawEmbeddingMatrix_mem_unitary (g : Group) :
    rawEmbeddingMatrix g ∈ Matrix.unitaryGroup BlockIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hAmem :
      (g.1 : Matrix (Fin 3) (Fin 3) ℂ) ∈
        Matrix.unitaryGroup (Fin 3) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup g.1.prop
  have hA := Matrix.mem_unitaryGroup_iff.mp hAmem
  have hB := Matrix.mem_unitaryGroup_iff.mp g.2.prop
  have hS := Matrix.mem_unitaryGroup_iff.mp (singletBlock_mem_unitary g.2)
  have hA' :
      (g.1 : Matrix (Fin 3) (Fin 3) ℂ) *
          Matrix.conjTranspose (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using hA
  have hB' :
      (g.2 : Matrix (Fin 2) (Fin 2) ℂ) *
          Matrix.conjTranspose (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using hB
  have hS' :
      singletBlock g.2 * Matrix.conjTranspose (singletBlock g.2) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using hS
  simp [rawEmbeddingMatrix, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    hA', hB', hS', Matrix.fromBlocks_one]

theorem rawEmbeddingMatrix_det (g : Group) :
    Matrix.det (rawEmbeddingMatrix g) = 1 := by
  have hAdet : Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    g.1.prop.2
  have hBdet := Matrix.det_of_mem_unitary g.2.prop
  rw [rawEmbeddingMatrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁]
  simp only [singletBlock, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  rw [hAdet, one_mul]
  exact hBdet.2

def rawEmbedding : Group →* Matrix BlockIndex BlockIndex ℂ where
  toFun := rawEmbeddingMatrix
  map_one' := rawEmbeddingMatrix_one
  map_mul' := rawEmbeddingMatrix_mul

def embeddingMatrix : Group →* Matrix (Fin 6) (Fin 6) ℂ :=
  (Matrix.reindexRingEquiv ℂ blockIndexEquiv).toMonoidHom.comp rawEmbedding

theorem embeddingMatrix_mem_unitary (g : Group) :
    embeddingMatrix g ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hraw := Matrix.mem_unitaryGroup_iff.mp (rawEmbeddingMatrix_mem_unitary g)
  change
    Matrix.reindex blockIndexEquiv blockIndexEquiv (rawEmbeddingMatrix g) *
        star (Matrix.reindex blockIndexEquiv blockIndexEquiv
          (rawEmbeddingMatrix g)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change
    (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (rawEmbeddingMatrix g) *
        (Matrix.reindexRingEquiv ℂ blockIndexEquiv)
          (star (rawEmbeddingMatrix g)) = 1
  rw [← map_mul, hraw]
  exact map_one (Matrix.reindexRingEquiv ℂ blockIndexEquiv)

theorem embeddingMatrix_det (g : Group) : Matrix.det (embeddingMatrix g) = 1 := by
  change Matrix.det
    (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawEmbeddingMatrix g)) = 1
  rw [Matrix.det_reindex_self, rawEmbeddingMatrix_det]

theorem embeddingMatrix_mem_specialUnitary (g : Group) :
    embeddingMatrix g ∈ Matrix.specialUnitaryGroup (Fin 6) ℂ :=
  ⟨embeddingMatrix_mem_unitary g, embeddingMatrix_det g⟩

def embedding : Group →* ActualRestriction.SU6 where
  toFun g := ⟨embeddingMatrix g, embeddingMatrix_mem_specialUnitary g⟩
  map_one' := Subtype.ext (map_one embeddingMatrix)
  map_mul' g h := Subtype.ext (map_mul embeddingMatrix g h)

theorem embedding_injective : Function.Injective embedding := by
  intro g h heq
  have hmatrix : embeddingMatrix g = embeddingMatrix h :=
    congrArg Subtype.val heq
  have hraw : rawEmbeddingMatrix g = rawEmbeddingMatrix h := by
    apply (Matrix.reindexRingEquiv ℂ blockIndexEquiv).injective
    exact hmatrix
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    have hij := congrArg
      (fun M : Matrix BlockIndex BlockIndex ℂ => M (Sum.inl i) (Sum.inl j))
      hraw
    simpa [rawEmbeddingMatrix] using hij
  · apply Subtype.ext
    ext i j
    have hij := congrArg
      (fun M : Matrix BlockIndex BlockIndex ℂ =>
        M (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))) hraw
    simpa [rawEmbeddingMatrix] using hij

/-!
## Lift of the color-neutral torus
-/

abbrev DiagonalPoint := ColorNeutralBranch.DiagonalPoint

def colorIndex (i : Fin 3) : Fin 6 := ⟨i, by omega⟩

def weakIndex (i : Fin 2) : Fin 6 := ⟨i + 3, by omega⟩

def colorMatrix (t : DiagonalPoint) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => t.coords (colorIndex i)

def weakMatrix (t : DiagonalPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => t.coords (weakIndex i)

theorem coord_mul_star (t : DiagonalPoint) (i : Fin 6) :
    t.coords i * star (t.coords i) = 1 := by
  have hmem :
      Matrix.diagonal t.toDiagonal.coords ∈ Matrix.unitaryGroup (Fin 6) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup t.toDiagonal.mem
  have hunit := Matrix.mem_unitaryGroup_iff.mp hmem
  rw [Matrix.star_eq_conjTranspose] at hunit
  have hstar :
      Matrix.conjTranspose (Matrix.diagonal t.toDiagonal.coords) =
        Matrix.diagonal (fun j => star (t.toDiagonal.coords j)) := by
    ext j k
    by_cases h : j = k
    · simp [Matrix.conjTranspose_apply, h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hstar, Matrix.diagonal_mul_diagonal] at hunit
  have hii := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M i i) hunit
  simpa [ColorNeutralBranch.DiagonalPoint.coords] using hii

theorem star_coord_eq_inv (t : DiagonalPoint) (i : Fin 6) :
    star (t.coords i) = (t.coords i)⁻¹ :=
  eq_inv_of_mul_eq_one_right (coord_mul_star t i)

theorem colorMatrix_mem_unitary (t : DiagonalPoint) :
    colorMatrix t ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold colorMatrix
  have hstar :
      Matrix.conjTranspose
          (Matrix.diagonal (fun i => t.coords (colorIndex i))) =
        Matrix.diagonal (fun i => star (t.coords (colorIndex i))) := by
    ext i j
    by_cases h : i = j
    · simp [Matrix.conjTranspose_apply, h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hstar, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simpa using coord_mul_star t (colorIndex i)
  · simp [h]

theorem weakMatrix_mem_unitary (t : DiagonalPoint) :
    weakMatrix t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold weakMatrix
  have hstar :
      Matrix.conjTranspose
          (Matrix.diagonal (fun i => t.coords (weakIndex i))) =
        Matrix.diagonal (fun i => star (t.coords (weakIndex i))) := by
    ext i j
    by_cases h : i = j
    · simp [Matrix.conjTranspose_apply, h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hstar, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simpa using coord_mul_star t (weakIndex i)
  · simp [h]

theorem colorMatrix_det (t : DiagonalPoint) : Matrix.det (colorMatrix t) = 1 := by
  simpa [colorMatrix, Matrix.det_diagonal, Fin.prod_univ_three, colorIndex,
    ColorNeutralBranch.DiagonalPoint.coords] using t.color_relation

theorem weakMatrix_det (t : DiagonalPoint) :
    Matrix.det (weakMatrix t) = t.coords 3 * t.coords 4 := by
  simp [weakMatrix, Matrix.det_diagonal, Fin.prod_univ_two, weakIndex]

def colorPoint (t : DiagonalPoint) : SU3 :=
  ⟨colorMatrix t, colorMatrix_mem_unitary t, colorMatrix_det t⟩

def weakPoint (t : DiagonalPoint) : U2 :=
  ⟨weakMatrix t, weakMatrix_mem_unitary t⟩

def torusPoint (t : DiagonalPoint) : Group :=
  (colorPoint t, weakPoint t)

theorem torusPoint_singlet (t : DiagonalPoint) :
    star (Matrix.det
        ((torusPoint t).2 : Matrix (Fin 2) (Fin 2) ℂ)) =
      t.coords 5 := by
  rw [star_det_eq_inv_det, show
    Matrix.det ((torusPoint t).2 : Matrix (Fin 2) (Fin 2) ℂ) =
      t.coords 3 * t.coords 4 by exact weakMatrix_det t]
  exact (t.coord5_eq_inv_tailProduct).symm

theorem singletBlock_weakPoint (t : DiagonalPoint) :
    singletBlock (weakPoint t) =
      Matrix.diagonal (fun _ : Fin 1 => t.coords 5) := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [singletBlock, Matrix.diagonal_apply_eq]
  simpa [torusPoint] using torusPoint_singlet t

theorem blockIndexEquiv_symm_zero :
    blockIndexEquiv.symm 0 = Sum.inl 0 := by decide

theorem blockIndexEquiv_symm_one :
    blockIndexEquiv.symm 1 = Sum.inl 1 := by decide

theorem blockIndexEquiv_symm_two :
    blockIndexEquiv.symm 2 = Sum.inl 2 := by decide

theorem blockIndexEquiv_symm_three :
    blockIndexEquiv.symm 3 = Sum.inr (Sum.inl 0) := by decide

theorem blockIndexEquiv_symm_four :
    blockIndexEquiv.symm 4 = Sum.inr (Sum.inl 1) := by decide

theorem blockIndexEquiv_symm_five :
    blockIndexEquiv.symm 5 = Sum.inr (Sum.inr 0) := by decide

theorem embeddingMatrix_torusPoint (t : DiagonalPoint) :
    embeddingMatrix (torusPoint t) = Matrix.diagonal t.toDiagonal.coords := by
  change
    Matrix.reindex blockIndexEquiv blockIndexEquiv
        (Matrix.fromBlocks (colorMatrix t) 0 0
          (Matrix.fromBlocks (weakMatrix t) 0 0
            (singletBlock (weakPoint t)))) =
      Matrix.diagonal t.toDiagonal.coords
  rw [singletBlock_weakPoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorMatrix, weakMatrix, colorIndex, weakIndex,
      blockIndexEquiv_symm_zero, blockIndexEquiv_symm_one,
      blockIndexEquiv_symm_two, blockIndexEquiv_symm_three,
      blockIndexEquiv_symm_four, blockIndexEquiv_symm_five,
      ColorNeutralBranch.DiagonalPoint.coords]

theorem embedding_torusPoint (t : DiagonalPoint) :
    embedding (torusPoint t) = t.toDiagonal.toSU6 := by
  apply Subtype.ext
  exact embeddingMatrix_torusPoint t

end


end ColorNeutralSMGroup
end GUT
