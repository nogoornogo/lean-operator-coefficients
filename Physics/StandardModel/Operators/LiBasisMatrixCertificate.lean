import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Exact certificates for the printed coordinate data in Li et al.
2201.04639v2 (4.38), (4.41), (4.44). These do not derive the differential
operator identities or establish the underlying operator quotients. -/
namespace GUT.LiBasisMatrixCertificate
noncomputable section
set_option autoImplicit false

def conversion : (Fin 6 → ℂ) ≃ₗ[ℂ] (Fin 6 → ℂ) where
  toFun x := ![-x 0 / 4 - x 2 / 4 + x 5, x 0 + x 2,
    Complex.I * (x 0 - x 2), Complex.I * (x 1 + x 3 + 2 * x 4),
    -2 * Complex.I * x 4, -2 * (x 1 - x 3)]
  invFun q := ![(q 1 - Complex.I * q 2) / 2,
    -Complex.I * (q 3 + q 4) / 2 - q 5 / 4,
    (q 1 + Complex.I * q 2) / 2,
    -Complex.I * (q 3 + q 4) / 2 + q 5 / 4,
    Complex.I * q 4 / 2, q 0 + q 1 / 4]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i; fin_cases i <;> simp <;> ring_nf <;> simp <;> ring
  right_inv x := by
    ext i; fin_cases i <;> simp <;> ring_nf <;> simp

def matrix38 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![-1/4,0,-1/4,0,0,1; 1,0,1,0,0,0;
     Complex.I,0,-Complex.I,0,0,0; 0,Complex.I,0,Complex.I,2*Complex.I,0;
     0,0,0,0,-2*Complex.I,0; 0,-2,0,2,0,0]

theorem matrix38_apply (x : Fin 6 → ℂ) : matrix38.mulVec x = conversion x := by
  ext i
  fin_cases i <;>
    simp [matrix38, conversion, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem rank38 : matrix38.rank = 6 := by
  unfold Matrix.rank
  have h : Function.Surjective matrix38.mulVecLin := by
    intro x
    refine ⟨conversion.symm x, ?_⟩
    change matrix38.mulVec (conversion.symm x) = x
    rw [matrix38_apply, LinearEquiv.apply_symm_apply]
  rw [LinearMap.range_eq_top.mpr h]
  simp

def matrix41 : Matrix (Fin 9) (Fin 4) ℂ :=
  !![1,0,0,0; 0,0,1,0; -1/2,1/2,0,0; 0,0,-1/2,1/2;
     0,1,0,0; 0,0,0,1; -1,-1,0,0; 1,-1,0,0; 0,0,0,0]

def matrix44 : Matrix (Fin 24) (Fin 4) ℂ :=
  !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1;
     -1,-1,0,0; 0,0,-1,-1; 2,0,0,0; 0,0,2,0;
     0,2,0,0; 0,0,0,2; -2,-2,0,0; 0,0,-2,-2;
     -2,-2,0,0; 0,0,-2,-2; 0,2,0,0; 0,0,0,2;
     2,0,0,0; 0,0,2,0; 4,8,0,0; 0,0,4,8;
     8,4,0,0; 0,0,8,4; 4,-4,0,0; 0,0,4,-4]

def synthesis41 : (Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun c := ![c 0 - c 2 / 2, c 2 / 2, c 1 - c 3 / 2, c 3 / 2]
  invFun x := ![x 0 + x 1, x 2 + x 3, 2 * x 1, 2 * x 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' z x := by ext i; fin_cases i <;> simp <;> ring
  left_inv x := by ext i; fin_cases i <;> simp <;> ring
  right_inv x := by ext i; fin_cases i <;> simp

def synthesis44 : (Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun c := ![c 0, c 2, c 1, c 3]
  invFun c := ![c 0, c 2, c 1, c 3]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' z x := by ext i; fin_cases i <;> simp
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

def basis41 := (Pi.basisFun ℂ (Fin 4)).map synthesis41
def basis44 := (Pi.basisFun ℂ (Fin 4)).map synthesis44

theorem basis41_row (i : Fin 4) : basis41 i = matrix41.row (i.castLE (by decide)) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis41, synthesis41, matrix41, Matrix.row, Pi.basisFun_apply,
      Pi.single_apply, Fin.ext_iff]

theorem basis44_row (i : Fin 4) : basis44 i = matrix44.row (i.castLE (by decide)) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis44, synthesis44, matrix44, Matrix.row, Pi.basisFun_apply,
      Pi.single_apply, Fin.ext_iff]

theorem span41 : Submodule.span ℂ (Set.range matrix41.row) = ⊤ := by
  apply top_unique
  rw [← basis41.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨i.castLE (by decide), (basis41_row i).symm⟩

theorem span44 : Submodule.span ℂ (Set.range matrix44.row) = ⊤ := by
  apply top_unique
  rw [← basis44.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨i.castLE (by decide), (basis44_row i).symm⟩

theorem rank41 : matrix41.rank = 4 := by
  rw [Matrix.rank_eq_finrank_span_row, span41]
  simp

theorem rank44 : matrix44.rank = 4 := by
  rw [Matrix.rank_eq_finrank_span_row, span44]
  simp

/-- Any basis in an independently supplied six-dimensional space transports
along the printed invertible coordinate conversion. No EFT premise is inferred. -/
def convertedBasis {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : (Fin 6 → ℂ) ≃ₗ[ℂ] V) :=
  (Pi.basisFun ℂ (Fin 6)).map (conversion.trans e)

end
end GUT.LiBasisMatrixCertificate
