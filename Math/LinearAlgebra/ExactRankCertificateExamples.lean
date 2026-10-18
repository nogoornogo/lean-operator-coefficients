import Math.LinearAlgebra.ExactRankCertificate

/-! Small rank examples derived by reconstruction on arbitrary vectors. -/
namespace Math.ExactRankExamples
open ExactRankCertificate
noncomputable section

/-- The last row is the sum of the first two, as is the last nonzero column. -/
def matrix0 : Matrix (Fin 3) (Fin 4) ℚ :=
  !![0, 1/2, 1, 3/2; 0, 1, 0, 1; 0, 3/2, 1, 5/2]

private def extend0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun u := ![u 0 / 2 + u 1, u 0, 3 * u 0 / 2 + u 1]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

private def read0 : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 1 + u 3, u 2 + u 3]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

private def project0 : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 1, u 0 - u 1 / 2]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

private def insert0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun u := ![0, u 0, u 1, 0]
  map_add' u v := by ext i; fin_cases i <;> (simp)
  map_smul' a u := by ext i; fin_cases i <;> (simp)

private def solve1 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![(u 1 - 3 * u 0) / 2, u 0]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

def certificate0 : Certificate (T := Fin 2) matrix0 :=
  Certificate.ofActions matrix0 extend0 read0 project0 insert0
    (by intro v; ext i; fin_cases i <;>
        simp [extend0, read0, matrix0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; all_goals ring)
    (by intro u; ext i; fin_cases i <;> simp [project0, extend0])
    (by intro u; ext i; fin_cases i <;> simp [read0, insert0])
theorem rank0 : (matrix0.map (Rat.castHom ℂ)).rank = 2 :=
  mapped_rank certificate0 (Rat.castHom ℂ)

/-- Swap the first output into the second input, then back-substitute. -/
def matrix1 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 2, 3]
def certificate1 : Certificate (T := Fin 2) matrix1 :=
  Certificate.ofActions matrix1 matrix1.mulVecLin LinearMap.id solve1 LinearMap.id
    (by intro v; rfl)
    (by intro u; ext i; fin_cases i <;>
        simp [solve1, matrix1, dotProduct, Fin.sum_univ_succ])
    (by intro u; rfl)
theorem rank1 : (matrix1.map (Rat.castHom ℂ)).rank = 2 :=
  mapped_rank certificate1 (Rat.castHom ℂ)

/-- Zero maps factor through the zero-dimensional space. -/
private def zeroCertificate (m n : ℕ) :
    Certificate (T := Fin 0) (0 : Matrix (Fin m) (Fin n) ℚ) where
  columns := 0
  rows := 0
  left := 0
  right := 0
  factor := by simp
  left_inverse := Subsingleton.elim _ _
  right_inverse := Subsingleton.elim _ _

def matrix2 : Matrix (Fin 2) (Fin 3) ℚ := 0
def certificate2 : Certificate (T := Fin 0) matrix2 := zeroCertificate 2 3
theorem rank2 : (matrix2.map (Rat.castHom ℂ)).rank = 0 :=
  mapped_rank certificate2 (Rat.castHom ℂ)

def matrix3 : Matrix (Fin 0) (Fin 3) ℚ := 0
def certificate3 : Certificate (T := Fin 0) matrix3 := zeroCertificate 0 3
theorem rank3 : (matrix3.map (Rat.castHom ℂ)).rank = 0 :=
  mapped_rank certificate3 (Rat.castHom ℂ)

def matrix4 : Matrix (Fin 3) (Fin 0) ℚ := 0
def certificate4 : Certificate (T := Fin 0) matrix4 := zeroCertificate 3 0
theorem rank4 : (matrix4.map (Rat.castHom ℂ)).rank = 0 :=
  mapped_rank certificate4 (Rat.castHom ℂ)

end
end Math.ExactRankExamples
