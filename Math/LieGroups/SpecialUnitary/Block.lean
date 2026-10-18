import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Topology.Algebra.UnitaryGroup

/-! Standard block inclusions SU(m) -> SU(m+k), including the empty
complement. The ambient coordinates are color-first when m = 5. -/

set_option autoImplicit false

namespace Math.SUN.Block

noncomputable section

abbrev Group (n : ℕ) := Matrix.specialUnitaryGroup (Fin n) ℂ
abbrev Index (m k : ℕ) := Fin m ⊕ Fin k
abbrev indexEquiv (m k : ℕ) : Index m k ≃ Fin (m + k) := finSumFinEquiv

def rawMatrix {m : ℕ} (k : ℕ) (A : Group m) : Matrix (Index m k) (Index m k) ℂ :=
  Matrix.fromBlocks A.val 0 0 1

def rawHom (m k : ℕ) : Group m →* Matrix (Index m k) (Index m k) ℂ where
  toFun := rawMatrix k
  map_one' := by simp [rawMatrix, Matrix.fromBlocks_one]
  map_mul' A B := by simp [rawMatrix, Matrix.fromBlocks_multiply]

theorem rawMatrix_unitary {m : ℕ} (k : ℕ) (A : Group m) :
    rawMatrix k A ∈ Matrix.unitaryGroup (Index m k) ℂ := by
  have h := Matrix.mem_unitaryGroup_iff.mp A.property.1
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose] at h ⊢
  simp [rawMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    h, Matrix.fromBlocks_one]

theorem rawMatrix_det {m : ℕ} (k : ℕ) (A : Group m) :
    Matrix.det (rawMatrix k A) = 1 := by
  rw [rawMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  exact A.property.2

def matrixHom (m k : ℕ) : Group m →* Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
  (Matrix.reindexRingEquiv ℂ (indexEquiv m k)).toMonoidHom.comp (rawHom m k)

theorem matrixHom_unitary {m : ℕ} (k : ℕ) (A : Group m) :
    matrixHom m k A ∈ Matrix.unitaryGroup (Fin (m + k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.mp (rawMatrix_unitary k A)
  change Matrix.reindex (indexEquiv m k) (indexEquiv m k) (rawMatrix k A) *
    star (Matrix.reindex (indexEquiv m k) (indexEquiv m k) (rawMatrix k A)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ (indexEquiv m k)) (rawMatrix k A) *
    (Matrix.reindexRingEquiv ℂ (indexEquiv m k)) (star (rawMatrix k A)) = 1
  rw [← map_mul, h, map_one]

theorem matrixHom_det {m : ℕ} (k : ℕ) (A : Group m) :
    Matrix.det (matrixHom m k A) = 1 := by
  change Matrix.det (Matrix.reindex (indexEquiv m k) (indexEquiv m k) (rawMatrix k A)) = 1
  rw [Matrix.det_reindex_self, rawMatrix_det]

def inclusion (m k : ℕ) : Group m →* Group (m + k) where
  toFun A := ⟨matrixHom m k A, matrixHom_unitary k A, matrixHom_det k A⟩
  map_one' := Subtype.ext (map_one (matrixHom m k))
  map_mul' A B := Subtype.ext (map_mul (matrixHom m k) A B)

theorem inclusion_injective (m k : ℕ) : Function.Injective (inclusion m k) := by
  intro A B he
  have hm : matrixHom m k A = matrixHom m k B := congrArg Subtype.val he
  have hr : rawMatrix k A = rawMatrix k B :=
    (Matrix.reindexRingEquiv ℂ (indexEquiv m k)).injective hm
  apply Subtype.ext
  ext i j
  exact congrArg (fun M : Matrix (Index m k) (Index m k) ℂ => M (.inl i) (.inl j)) hr

theorem inclusion_continuous (m k : ℕ) : Continuous (inclusion m k) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun A : Group m =>
    Matrix.reindex (indexEquiv m k) (indexEquiv m k) (rawMatrix k A))
  unfold rawMatrix
  fun_prop

def continuousInclusion (m k : ℕ) : Group m →ₜ* Group (m + k) where
  toMonoidHom := inclusion m k
  continuous_toFun := inclusion_continuous m k

theorem inclusion_left {m k : ℕ} (A : Group m) (i j : Fin m) :
    (inclusion m k A).val (i.castAdd k) (j.castAdd k) = A.val i j := by
  change rawMatrix k A ((indexEquiv m k).symm (indexEquiv m k (.inl i)))
    ((indexEquiv m k).symm (indexEquiv m k (.inl j))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem inclusion_right {m k : ℕ} (A : Group m) (i j : Fin k) :
    (inclusion m k A).val (i.natAdd m) (j.natAdd m) = (1 : Matrix (Fin k) (Fin k) ℂ) i j := by
  change rawMatrix k A ((indexEquiv m k).symm (indexEquiv m k (.inr i)))
    ((indexEquiv m k).symm (indexEquiv m k (.inr j))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem inclusion_zero (m : ℕ) : inclusion m 0 = MonoidHom.id (Group m) := by
  ext A i j
  exact inclusion_left A i j

theorem dimension_parameter {n : ℕ} (h : 5 ≤ n) : ∃ k, n = 5 + k :=
  ⟨n - 5, (Nat.add_sub_of_le h).symm⟩

theorem exists_inclusion {m n : ℕ} (h : m ≤ n) :
    ∃ i : Group m →* Group n, Function.Injective i ∧ Continuous i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨inclusion m k, inclusion_injective m k, inclusion_continuous m k⟩

end

end Math.SUN.Block
