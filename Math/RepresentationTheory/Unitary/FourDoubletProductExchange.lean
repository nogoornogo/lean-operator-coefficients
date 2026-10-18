import Math.RepresentationTheory.Unitary.FourDoubletInvariant

/-! Explicit adjacent exchanges of the two-by-two epsilon-product basis.
The same formulas apply to weak doublets and left Weyl spinors. -/
namespace Math.FourDoubletProductExchange
set_option autoImplicit false
noncomputable section
open FourDoubletInvariant

abbrev Coordinates := Fin 2 → Fin 2 → ℂ

def evaluate (k : Coordinates) (a b c d s t v w : Space) : ℂ :=
  k 0 0 * (eps a b * eps c d) * (eps s t * eps v w) +
  k 0 1 * (eps a b * eps c d) * (eps s v * eps t w) +
  k 1 0 * (eps a c * eps b d) * (eps s t * eps v w) +
  k 1 1 * (eps a c * eps b d) * (eps s v * eps t w)

def probe (i : Fin 2) : Fin 4 → Space :=
  if i = 0 then ![basis 0, basis 1, basis 0, basis 1]
  else ![basis 0, basis 0, basis 1, basis 1]

theorem evaluate_probe (k : Coordinates) (i j : Fin 2) :
    evaluate k (probe i 0) (probe i 1) (probe i 2) (probe i 3)
      (probe j 0) (probe j 1) (probe j 2) (probe j 3) = k i j := by
  fin_cases i <;> fin_cases j <;> simp [evaluate, probe, eps, basis]

theorem ext {k l : Coordinates}
    (h : ∀ a b c d s t v w, evaluate k a b c d s t v w = evaluate l a b c d s t v w) :
    k = l := by
  funext i j
  simpa only [evaluate_probe] using h (probe i 0) (probe i 1) (probe i 2) (probe i 3)
    (probe j 0) (probe j 1) (probe j 2) (probe j 3)

def exchange01 (k : Coordinates) : Coordinates :=
  ![![k 0 0 + k 0 1 + k 1 0 + k 1 1, -k 0 1 - k 1 1],
    ![-k 1 0 - k 1 1, k 1 1]]

def exchange12 (k : Coordinates) : Coordinates :=
  ![![k 1 1, k 1 0], ![k 0 1, k 0 0]]

theorem exchange01_add (k l : Coordinates) : exchange01 (k + l) = exchange01 k + exchange01 l := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange01] <;> ring

theorem exchange12_add (k l : Coordinates) : exchange12 (k + l) = exchange12 k + exchange12 l := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exchange01_smul (c : ℂ) (k : Coordinates) : exchange01 (c • k) = c • exchange01 k := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange01, smul_eq_mul] <;> ring

theorem exchange12_smul (c : ℂ) (k : Coordinates) : exchange12 (c • k) = c • exchange12 k := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem evaluate_exchange01 (k : Coordinates) (a b c d s t v w : Space) :
    evaluate k b a c d t s v w = evaluate (exchange01 k) a b c d s t v w := by
  simp only [evaluate, exchange01, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, eps]
  ring

theorem evaluate_exchange12 (k : Coordinates) (a b c d s t v w : Space) :
    evaluate k a c b d s v t w = evaluate (exchange12 k) a b c d s t v w := by
  simp only [evaluate, exchange12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem exchange01_involutive (k : Coordinates) : exchange01 (exchange01 k) = k := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange01]
  ring

theorem exchange12_involutive (k : Coordinates) : exchange12 (exchange12 k) = k := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The braid relation verifies compatibility of the adjacent exchanges. -/
theorem braid (k : Coordinates) :
    exchange01 (exchange12 (exchange01 k)) = exchange12 (exchange01 (exchange12 k)) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange01, exchange12] <;> ring

end
end Math.FourDoubletProductExchange
