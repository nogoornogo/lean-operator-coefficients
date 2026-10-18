import GUT.SU6.Characters.AmbientCharacterBridge
import GUT.SU6.SelectionRules.FlippedBranch.PhysicalRestrictionBridge
import Mathlib.LinearAlgebra.Matrix.Reindex

open Math

/-!
# The concrete standard U(5) subgroup of SU(6)

The standard branch is naturally contained in the block subgroup

`U(5) -> SU(6),  A |-> diag(A, det(A)^-1)`.

Its maximal torus is the full determinant-one diagonal torus used by
`AmbientLaurent`: the first five coordinates are arbitrary phases and the
sixth is their inverse product.  This file constructs the actual group
embedding, proves its injectivity, lifts every ambient diagonal point through
it, and identifies actual restricted trace characters on those points.
-/

namespace GUT
namespace StandardU5Group

noncomputable section

abbrev U5 := Matrix.unitaryGroup (Fin 5) ℂ
abbrev SU6 := ActualRestriction.SU6
abbrev BlockIndex := Fin 5 ⊕ Fin 1

def blockIndexEquiv : BlockIndex ≃ Fin 6 :=
  @finSumFinEquiv 5 1

def singletBlock (A : U5) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal fun _ => star (Matrix.det (A : Matrix (Fin 5) (Fin 5) ℂ))

theorem star_det_eq_inv_det (A : U5) :
    star (Matrix.det (A : Matrix (Fin 5) (Fin 5) ℂ)) =
      (Matrix.det (A : Matrix (Fin 5) (Fin 5) ℂ))⁻¹ := by
  have hunit := Matrix.det_of_mem_unitary A.prop
  have hne : Matrix.det (A : Matrix (Fin 5) (Fin 5) ℂ) ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit A).ne_zero
  exact (mul_eq_one_iff_eq_inv₀ hne).mp hunit.1

def rawEmbeddingMatrix (A : U5) : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (A : Matrix (Fin 5) (Fin 5) ℂ) 0 0 (singletBlock A)

theorem rawEmbeddingMatrix_one : rawEmbeddingMatrix 1 = 1 := by
  simp [rawEmbeddingMatrix, singletBlock, Matrix.fromBlocks_one]

theorem rawEmbeddingMatrix_mul (A B : U5) :
    rawEmbeddingMatrix (A * B) =
      rawEmbeddingMatrix A * rawEmbeddingMatrix B := by
  simp [rawEmbeddingMatrix, singletBlock, Matrix.fromBlocks_multiply,
    Matrix.det_mul]

theorem singletBlock_mem_unitary (A : U5) :
    singletBlock A ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hdet := Matrix.det_of_mem_unitary A.prop
  ext i j
  fin_cases i
  fin_cases j
  simpa [singletBlock, Matrix.mul_apply] using hdet.1

theorem rawEmbeddingMatrix_mem_unitary (A : U5) :
    rawEmbeddingMatrix A ∈ Matrix.unitaryGroup BlockIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hA := Matrix.mem_unitaryGroup_iff.mp A.prop
  have hS := Matrix.mem_unitaryGroup_iff.mp (singletBlock_mem_unitary A)
  have hA' :
      (A : Matrix (Fin 5) (Fin 5) ℂ) *
          Matrix.conjTranspose (A : Matrix (Fin 5) (Fin 5) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using hA
  have hS' :
      singletBlock A * Matrix.conjTranspose (singletBlock A) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using hS
  simp [rawEmbeddingMatrix, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    hA', hS', Matrix.fromBlocks_one]

theorem rawEmbeddingMatrix_det (A : U5) :
    Matrix.det (rawEmbeddingMatrix A) = 1 := by
  have hdet := Matrix.det_of_mem_unitary A.prop
  rw [rawEmbeddingMatrix, Matrix.det_fromBlocks_zero₂₁]
  simp only [singletBlock, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  exact hdet.2

def rawEmbedding : U5 →* Matrix BlockIndex BlockIndex ℂ where
  toFun := rawEmbeddingMatrix
  map_one' := rawEmbeddingMatrix_one
  map_mul' := rawEmbeddingMatrix_mul

def embeddingMatrix : U5 →* Matrix (Fin 6) (Fin 6) ℂ :=
  (Matrix.reindexRingEquiv ℂ blockIndexEquiv).toMonoidHom.comp rawEmbedding

theorem embeddingMatrix_mem_unitary (A : U5) :
    embeddingMatrix A ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hraw := Matrix.mem_unitaryGroup_iff.mp
    (rawEmbeddingMatrix_mem_unitary A)
  change
    Matrix.reindex blockIndexEquiv blockIndexEquiv (rawEmbeddingMatrix A) *
        star (Matrix.reindex blockIndexEquiv blockIndexEquiv
          (rawEmbeddingMatrix A)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change
    (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (rawEmbeddingMatrix A) *
        (Matrix.reindexRingEquiv ℂ blockIndexEquiv)
          (star (rawEmbeddingMatrix A)) = 1
  rw [← map_mul, hraw]
  exact map_one (Matrix.reindexRingEquiv ℂ blockIndexEquiv)

theorem embeddingMatrix_det (A : U5) :
    Matrix.det (embeddingMatrix A) = 1 := by
  change Matrix.det
    (Matrix.reindex blockIndexEquiv blockIndexEquiv
      (rawEmbeddingMatrix A)) = 1
  rw [Matrix.det_reindex_self, rawEmbeddingMatrix_det]

theorem embeddingMatrix_mem_specialUnitary (A : U5) :
    embeddingMatrix A ∈ Matrix.specialUnitaryGroup (Fin 6) ℂ :=
  ⟨embeddingMatrix_mem_unitary A, embeddingMatrix_det A⟩

/-- The concrete standard block embedding `U(5) -> SU(6)`. -/
def embedding : U5 →* SU6 where
  toFun A := ⟨embeddingMatrix A, embeddingMatrix_mem_specialUnitary A⟩
  map_one' := Subtype.ext (map_one embeddingMatrix)
  map_mul' A B := Subtype.ext (map_mul embeddingMatrix A B)

theorem embedding_injective : Function.Injective embedding := by
  intro A B h
  have hmatrix : embeddingMatrix A = embeddingMatrix B :=
    congrArg Subtype.val h
  have hraw : rawEmbeddingMatrix A = rawEmbeddingMatrix B := by
    apply (Matrix.reindexRingEquiv ℂ blockIndexEquiv).injective
    exact hmatrix
  apply Subtype.ext
  ext i j
  have hij := congrArg
    (fun M : Matrix BlockIndex BlockIndex ℂ => M (Sum.inl i) (Sum.inl j))
    hraw
  simpa [rawEmbeddingMatrix] using hij

/-!
## The actual diagonal torus lift
-/

abbrev DiagonalPoint := AmbientLaurent.DiagonalPoint

def torusMatrix (t : DiagonalPoint) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun i => t.coords i.castSucc

theorem torusMatrix_mem_unitary (t : DiagonalPoint) :
    torusMatrix t ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold torusMatrix
  have hstar :
      Matrix.conjTranspose
          (Matrix.diagonal (fun i : Fin 5 => t.coords i.castSucc)) =
        Matrix.diagonal (fun i => star (t.coords i.castSucc)) := by
    ext i j
    by_cases h : i = j
    · simp [Matrix.conjTranspose_apply, h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [hstar, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simpa using AmbientLaurent.DiagonalPoint.coord_mul_star t i.castSucc
  · simp [h]

theorem torusMatrix_det (t : DiagonalPoint) :
    Matrix.det (torusMatrix t) = ∏ i : Fin 5, t.coords i.castSucc := by
  simp [torusMatrix, Matrix.det_diagonal]

def torusPoint (t : DiagonalPoint) : U5 :=
  ⟨torusMatrix t, torusMatrix_mem_unitary t⟩

theorem torusPoint_singlet (t : DiagonalPoint) :
    star (Matrix.det
        ((torusPoint t : U5) : Matrix (Fin 5) (Fin 5) ℂ)) =
      t.coords (Fin.last 5) := by
  rw [star_det_eq_inv_det, show
    Matrix.det ((torusPoint t : U5) : Matrix (Fin 5) (Fin 5) ℂ) =
      ∏ i : Fin 5, t.coords i.castSucc by exact torusMatrix_det t]
  have hprod := AmbientLaurent.DiagonalPoint.det_product t
  rw [Fin.prod_univ_castSucc] at hprod
  exact (eq_inv_of_mul_eq_one_right hprod).symm

theorem singletBlock_torusPoint (t : DiagonalPoint) :
    singletBlock (torusPoint t) =
      Matrix.diagonal (fun _ : Fin 1 => t.coords (Fin.last 5)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [singletBlock, Matrix.diagonal_apply_eq]
  exact torusPoint_singlet t

theorem blockIndexEquiv_symm_zero :
    blockIndexEquiv.symm 0 = Sum.inl 0 := by decide

theorem blockIndexEquiv_symm_one :
    blockIndexEquiv.symm 1 = Sum.inl 1 := by decide

theorem blockIndexEquiv_symm_two :
    blockIndexEquiv.symm 2 = Sum.inl 2 := by decide

theorem blockIndexEquiv_symm_three :
    blockIndexEquiv.symm 3 = Sum.inl 3 := by decide

theorem blockIndexEquiv_symm_four :
    blockIndexEquiv.symm 4 = Sum.inl 4 := by decide

theorem blockIndexEquiv_symm_five :
    blockIndexEquiv.symm 5 = Sum.inr 0 := by decide

theorem embeddingMatrix_torusPoint (t : DiagonalPoint) :
    embeddingMatrix (torusPoint t) = Matrix.diagonal t.coords := by
  change
    Matrix.reindex blockIndexEquiv blockIndexEquiv
        (Matrix.fromBlocks (torusMatrix t) 0 0
          (singletBlock (torusPoint t))) =
      Matrix.diagonal t.coords
  rw [singletBlock_torusPoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, blockIndexEquiv_symm_zero,
      blockIndexEquiv_symm_one, blockIndexEquiv_symm_two,
      blockIndexEquiv_symm_three, blockIndexEquiv_symm_four,
      blockIndexEquiv_symm_five]

theorem embedding_torusPoint (t : DiagonalPoint) :
    embedding (torusPoint t) = t.toSU6 := by
  apply Subtype.ext
  exact embeddingMatrix_torusPoint t

/-!
## Restricted characters on the standard subgroup
-/

abbrev ActualRepresentation := VirtualRestriction.ActualSU6Representation
abbrev FiniteVirtualRepresentation :=
  VirtualRestriction.FiniteVirtualSU6Representation

def restrictActual (R : ActualRepresentation) :
    PhysicalRestrictionBridge.ActualGroupRepresentation U5 :=
  PhysicalRestrictionBridge.restrictActual embedding R

theorem restrictActual_character_torus
    (R : ActualRepresentation) (t : DiagonalPoint) :
    (restrictActual R).character (torusPoint t) =
      AmbientCharacterBridge.actualRestrictedCharacter R t := by
  calc
    (restrictActual R).character (torusPoint t) =
        R.rho.character (embedding (torusPoint t)) := rfl
    _ = R.rho.character t.toSU6 := by rw [embedding_torusPoint]
    _ = AmbientCharacterBridge.actualRestrictedCharacter R t := rfl

def restrictVirtual (chi : FiniteVirtualRepresentation) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation U5 :=
  PhysicalRestrictionBridge.restrictVirtual embedding chi

theorem restrictVirtual_character_torus
    (chi : FiniteVirtualRepresentation) (t : DiagonalPoint) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (restrictVirtual chi) (torusPoint t) =
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi t := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp only [restrictVirtual, PhysicalRestrictionBridge.restrictVirtual,
        PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character,
        PhysicalRestrictionBridge.VirtualGroupSummand.character,
        PhysicalRestrictionBridge.restrictSummand,
        AmbientCharacterBridge.finiteVirtualRestrictedCharacter,
        AmbientCharacterBridge.summandRestrictedCharacter]
      change
        (s.coeff : ℂ) * (restrictActual s.rep).character (torusPoint t) +
            PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
              (restrictVirtual ss) (torusPoint t) =
          (s.coeff : ℂ) *
              AmbientCharacterBridge.actualRestrictedCharacter s.rep t +
            AmbientCharacterBridge.finiteVirtualRestrictedCharacter ss t
      rw [restrictActual_character_torus, ih]

theorem actualModel_evaluates_restrictedU5
    (R : ActualRepresentation)
    (M : AmbientCharacterBridge.ActualAmbientLaurentModel R.rho)
    (t : DiagonalPoint) :
    AmbientLaurent.diagonalEval M.poly t =
      (restrictActual R).character (torusPoint t) := by
  calc
    AmbientLaurent.diagonalEval M.poly t =
        AmbientCharacterBridge.actualRestrictedCharacter R t :=
      M.evaluates_character t
    _ = (restrictActual R).character (torusPoint t) :=
      (restrictActual_character_torus R t).symm

theorem virtualModel_evaluates_restrictedU5
    (chi : FiniteVirtualRepresentation)
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (t : DiagonalPoint) :
    AmbientLaurent.diagonalEval M.poly t =
      PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (restrictVirtual chi) (torusPoint t) := by
  calc
    AmbientLaurent.diagonalEval M.poly t =
        AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi t :=
      M.evaluates_character t
    _ = PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (restrictVirtual chi) (torusPoint t) :=
      (restrictVirtual_character_torus chi t).symm

end
end StandardU5Group
end GUT
