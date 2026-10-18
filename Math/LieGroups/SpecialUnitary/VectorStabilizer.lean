import Math.LieGroups.SpecialUnitary.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The stabilizer of the last standard vector in SU(n+1) is exactly the
standard SU(n) block, as a topological group. No sphere-bundle claim yet. -/

set_option autoImplicit false
open Matrix

namespace Math.SUN.VectorStabilizer

noncomputable section

open Block

def lastVector (n : ℕ) : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1

def subgroup (n : ℕ) : Subgroup (Block.Group (n + 1)) where
  carrier := {g | g.val *ᵥ lastVector n = lastVector n}
  one_mem' := Matrix.one_mulVec _
  mul_mem' {g h} hg hh := by
    change (g.val * h.val) *ᵥ lastVector n = _
    rw [← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' {g} hg := by
    have h := congrArg (fun v => g⁻¹.val *ᵥ v) hg
    have hi : g⁻¹.val * g.val = 1 := g.property.1.1
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] at h
    exact h.symm

theorem last_column {n : ℕ} (g : subgroup n) (i : Fin (n + 1)) :
    g.val.val i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
  have h := congrFun g.property i
  simpa [lastVector, Matrix.mulVec_single, Pi.single_apply] using h

theorem last_row {n : ℕ} (g : subgroup n) (i : Fin (n + 1)) :
    g.val.val (Fin.last n) i = if i = Fin.last n then 1 else 0 := by
  have h := congrArg star (last_column g⁻¹ i)
  have hi : g⁻¹.val.val i (Fin.last n) = star (g.val.val (Fin.last n) i) := rfl
  rw [hi, star_star] at h
  simpa using h

def block {n : ℕ} (g : subgroup n) : Matrix (Fin n) (Fin n) ℂ :=
  g.val.val.submatrix Fin.castSucc Fin.castSucc

def splitMatrix {n : ℕ} (g : subgroup n) : Matrix (Index n 1) (Index n 1) ℂ :=
  g.val.val.submatrix (indexEquiv n 1) (indexEquiv n 1)

theorem splitMatrix_eq {n : ℕ} (g : subgroup n) :
    splitMatrix g = Matrix.fromBlocks (block g) 0 0 1 := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change g.val.val i.castSucc (Fin.last n) = 0
      simpa using last_column g i.castSucc
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j with
    | inl j =>
      change g.val.val (Fin.last n) j.castSucc = 0
      simpa using last_row g j.castSucc
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change g.val.val (Fin.last n) (Fin.last n) = 1
      simpa using last_column g (Fin.last n)

theorem splitMatrix_unitary {n : ℕ} (g : subgroup n) :
    splitMatrix g ∈ Matrix.unitaryGroup (Index n 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.reindex (indexEquiv n 1).symm (indexEquiv n 1).symm g.val.val *
    star (Matrix.reindex (indexEquiv n 1).symm (indexEquiv n 1).symm g.val.val) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ (indexEquiv n 1).symm) g.val.val *
    (Matrix.reindexRingEquiv ℂ (indexEquiv n 1).symm) (star g.val.val) = 1
  rw [← map_mul, (Matrix.mem_unitaryGroup_iff.mp g.val.property.1), map_one]

theorem block_unitary {n : ℕ} (g : subgroup n) :
    block g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h := Matrix.mem_unitaryGroup_iff.mp (splitMatrix_unitary g)
  rw [splitMatrix_eq] at h
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one] at h
  ext i j
  simpa [Matrix.one_apply, Matrix.star_eq_conjTranspose] using
    congrArg (fun A => A (.inl i) (.inl j)) h

theorem block_det {n : ℕ} (g : subgroup n) : (block g).det = 1 := by
  have hd : (splitMatrix g).det = 1 := by
    rw [splitMatrix, Matrix.det_submatrix_equiv_self]
    exact g.val.property.2
  rwa [splitMatrix_eq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at hd

def lower {n : ℕ} (g : subgroup n) : Block.Group n :=
  ⟨block g, block_unitary g, block_det g⟩

theorem inclusion_lower {n : ℕ} (g : subgroup n) : inclusion n 1 (lower g) = g.val := by
  apply Subtype.ext
  apply (Matrix.reindexRingEquiv ℂ (indexEquiv n 1)).symm.injective
  change (Matrix.reindexRingEquiv ℂ (indexEquiv n 1)).symm
      ((Matrix.reindexRingEquiv ℂ (indexEquiv n 1)) (rawMatrix 1 (lower g))) =
    splitMatrix g
  rw [RingEquiv.symm_apply_apply, splitMatrix_eq]
  rfl

theorem inclusion_mem (n : ℕ) (g : Block.Group n) : inclusion n 1 g ∈ subgroup n := by
  change (inclusion n 1 g).val *ᵥ lastVector n = lastVector n
  ext i
  simp only [lastVector, Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  change Matrix.reindex (indexEquiv n 1) (indexEquiv n 1) (rawMatrix 1 g)
    i (Fin.last n) = (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℂ) i
  have he : Fin.last n = indexEquiv n 1 (.inr 0) := rfl
  rw [he]
  obtain ⟨i, rfl⟩ := (indexEquiv n 1).surjective i
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    change 0 = (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℂ) i.castSucc
    simp
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change 1 = (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℂ) (Fin.last n)
    simp

def inclusionToStabilizer (n : ℕ) : Block.Group n →* subgroup n :=
  (inclusion n 1).codRestrict (subgroup n) (inclusion_mem n)

theorem inclusionToStabilizer_injective (n : ℕ) :
    Function.Injective (inclusionToStabilizer n) := by
  intro g h he
  exact inclusion_injective n 1 (congrArg Subtype.val he)

theorem inclusionToStabilizer_surjective (n : ℕ) :
    Function.Surjective (inclusionToStabilizer n) :=
  fun g => ⟨lower g, Subtype.ext (inclusion_lower g)⟩

theorem inclusionToStabilizer_continuous (n : ℕ) :
    Continuous (inclusionToStabilizer n) :=
  continuous_induced_rng.mpr (inclusion_continuous n 1)

def equiv (n : ℕ) : Block.Group n ≃ₜ* subgroup n :=
  ContinuousMulEquiv.mk'
    (((inclusionToStabilizer_continuous n).isClosedEmbedding
      (inclusionToStabilizer_injective n)).isEmbedding.toHomeomorphOfSurjective
        (inclusionToStabilizer_surjective n))
    (map_mul (inclusionToStabilizer n))

theorem equiv_apply (n : ℕ) (g : Block.Group n) : equiv n g = inclusionToStabilizer n g := rfl

theorem equiv_symm_apply {n : ℕ} (g : subgroup n) : (equiv n).symm g = lower g := by
  apply (equiv n).injective
  rw [ContinuousMulEquiv.apply_symm_apply, equiv_apply]
  exact (Subtype.ext (inclusion_lower g)).symm

end

end Math.SUN.VectorStabilizer
