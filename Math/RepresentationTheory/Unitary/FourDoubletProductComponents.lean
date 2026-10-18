import Math.RepresentationTheory.Unitary.FourDoubletProductExchange
import Mathlib.Tactic

/-! Explicit trivial, sign and two-dimensional components of the local
three-slot exchange dictionary. -/
namespace Math.FourDoubletProductComponents
set_option autoImplicit false
noncomputable section
open FourDoubletProductExchange

abbrev Components := Fin 4 → ℂ

def assemble (z : Components) : Coordinates :=
  ![![2*z 0 + z 2, -z 0 + z 1 + z 3],
    ![-z 0 - z 1 + z 3, 2*z 0 - z 2 - z 3]]

def extract (k : Coordinates) : Components := ![
  (2*(k 0 0 + k 1 1) + k 0 1 + k 1 0)/6,
  (k 0 1 - k 1 0)/2,
  k 0 0 - (2*(k 0 0 + k 1 1) + k 0 1 + k 1 0)/3,
  (k 0 0 + k 1 1 + 2*(k 0 1 + k 1 0))/3]

@[simp] theorem extract_assemble (z : Components) : extract (assemble z) = z := by
  funext i
  fin_cases i <;> simp [extract, assemble] <;> ring

@[simp] theorem assemble_extract (k : Coordinates) : assemble (extract k) = k := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [extract, assemble] <;> ring

def equiv : Coordinates ≃ₗ[ℂ] Components where
  toFun := extract
  invFun := assemble
  left_inv := assemble_extract
  right_inv := extract_assemble
  map_add' k m := by
    funext i
    fin_cases i <;> simp [extract] <;> ring
  map_smul' c k := by
    funext i
    fin_cases i <;> simp [extract, smul_eq_mul] <;> ring

def action01 (z : Components) : Components :=
  ![z 0, -z 1, z 3, z 2]

def action12 (z : Components) : Components :=
  ![z 0, -z 1, -z 2 - z 3, z 3]

theorem exchange01_assemble (z : Components) :
    exchange01 (assemble z) = assemble (action01 z) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange01, assemble, action01] <;> ring

theorem exchange12_assemble (z : Components) :
    exchange12 (assemble z) = assemble (action12 z) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exchange12, assemble, action12] <;> ring

theorem extract_exchange01 (k : Coordinates) :
    extract (exchange01 k) = action01 (extract k) := by
  rw [← assemble_extract k, exchange01_assemble, extract_assemble, extract_assemble]

theorem extract_exchange12 (k : Coordinates) :
    extract (exchange12 k) = action12 (extract k) := by
  rw [← assemble_extract k, exchange12_assemble, extract_assemble, extract_assemble]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def assembleModule (z : Fin 4 → V) : Fin 2 → Fin 2 → V :=
  ![![(2 : ℂ) • z 0 + z 2, -z 0 + z 1 + z 3],
    ![-z 0 - z 1 + z 3, (2 : ℂ) • z 0 - z 2 - z 3]]

def extractModule (k : Fin 2 → Fin 2 → V) : Fin 4 → V := ![
  (1/6 : ℂ) • ((2 : ℂ) • (k 0 0 + k 1 1) + k 0 1 + k 1 0),
  (1/2 : ℂ) • (k 0 1 - k 1 0),
  k 0 0 - (1/3 : ℂ) • ((2 : ℂ) • (k 0 0 + k 1 1) + k 0 1 + k 1 0),
  (1/3 : ℂ) • (k 0 0 + k 1 1 + (2 : ℂ) • (k 0 1 + k 1 0))]

def moduleEquiv : (Fin 2 → Fin 2 → V) ≃ₗ[ℂ] (Fin 4 → V) where
  toFun := extractModule
  invFun := assembleModule
  left_inv k := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [assembleModule, extractModule] <;> module
  right_inv z := by
    funext i
    fin_cases i <;> simp [assembleModule, extractModule] <;> module
  map_add' k m := by
    funext i
    fin_cases i <;> simp [extractModule] <;> module
  map_smul' c k := by
    funext i
    fin_cases i <;> simp [extractModule] <;> module

end
end Math.FourDoubletProductComponents
