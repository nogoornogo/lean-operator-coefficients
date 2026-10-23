import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExtension
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Explicit 2+3 coordinate changes on the color and spin factors.
The inverse formulas are proved symbolically for arbitrary inputs, using only
five cases at a time. Their product reduces a 25-dimensional problem to
4-, 6-, 6- and 9-dimensional blocks, without a dense inverse table. -/
namespace Physics.LiSixQuarkBlockCoordinates
noncomputable section
open LiSixQuarkExtension
open scoped TensorProduct
abbrev Split := (Fin 2 → ℂ) × (Fin 3 → ℂ)

def colorExtract (x : Fin 5 → ℂ) : Split :=
  (![x 1 / 2, x 2 / 2],
   ![x 0 + (x 1 - x 2) / 2, x 3 + x 1 / 2, x 4 + x 2 / 2])

def colorAssemble (v : Split) : Fin 5 → ℂ :=
  ![-v.1 0 + v.1 1 + v.2 0, 2*v.1 0, 2*v.1 1,
    -v.1 0 + v.2 1, -v.1 1 + v.2 2]

/-- First two coordinates are the named color pair; the complement uses
C₀,C₃,C₄. All coefficients are given by a five-equation reconstruction. -/
def colorEquiv : (Fin 5 → ℂ) ≃ₗ[ℂ] Split where
  toFun := colorExtract
  invFun := colorAssemble
  left_inv x := by
    ext i
    fin_cases i <;> simp [colorExtract, colorAssemble] <;> ring
  right_inv v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [colorExtract, colorAssemble]
    ring
  map_add' x y := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [colorExtract] <;> ring
  map_smul' z x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [colorExtract] <;> ring

def spinExtract (x : Fin 5 → ℂ) : Split :=
  (![(2*x 0 + 2*x 2 - x 1 - x 3 - x 4)/6,
     (x 0 + x 2 + x 1 + x 3 - 2*x 4)/6],
   ![(x 0 - x 2 + x 4)/2, (x 1 - x 3 + x 4)/2, x 4])

def spinAssemble (v : Split) : Fin 5 → ℂ :=
  ![v.1 0 + v.1 1 + v.2 0, -v.1 0 + 2*v.1 1 + v.2 1,
    v.1 0 + v.1 1 - v.2 0 + v.2 2,
    -v.1 0 + 2*v.1 1 - v.2 1 + v.2 2, v.2 2]

/-- First two coordinates are X,Y; the complement is
S₀-S₂, S₁-S₃, S₂+S₃+S₄. -/
def spinEquiv : (Fin 5 → ℂ) ≃ₗ[ℂ] Split where
  toFun := spinExtract
  invFun := spinAssemble
  left_inv x := by
    ext i
    fin_cases i <;> simp [spinExtract, spinAssemble] <;> ring
  right_inv v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;>
      simp [spinExtract, spinAssemble] <;> ring
  map_add' x y := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [spinExtract] <;> ring
  map_smul' z x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [spinExtract] <;> ring

/-- These are identities of families, not numerical rank assertions. -/
theorem color_pair (a b : ℂ) : colorAssemble (![a,b], 0) =
    fun p => a * extraColorFirst p + b * extraColorSecond p := by
  ext p
  fin_cases p <;> simp [colorAssemble] <;> ring

theorem spin_pair (a b : ℂ) : spinAssemble (![a,b], 0) =
    fun q => a * extraSpinFirst q + b * extraSpinSecond q := by
  ext q
  fin_cases q <;> simp [spinAssemble] <;> ring

abbrev V2 := Fin 2 → ℂ
abbrev V3 := Fin 3 → ℂ
abbrev Blocks := ((V2 ⊗[ℂ] V2) × (V2 ⊗[ℂ] V3)) ×
  ((V3 ⊗[ℂ] V2) × (V3 ⊗[ℂ] V3))

def transpose : (Fin 5 → Fin 5 → ℂ) ≃ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) where
  toFun c p q := c q p
  invFun c p q := c q p
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual local arrays, not just a dimension count, split into the four
product blocks. Tensor distribution supplies both inverse identities. -/
def localBlocks : (Fin 5 → Fin 5 → ℂ) ≃ₗ[ℂ] Blocks :=
  transpose.trans ((TensorProduct.piScalarRight ℂ ℂ (Fin 5 → ℂ) (Fin 5)).symm.trans
    ((TensorProduct.congr colorEquiv spinEquiv).trans
      ((TensorProduct.prodLeft ℂ ℂ V2 V3 Split).trans
        ((TensorProduct.prodRight ℂ ℂ V2 V2 V3).prodCongr
          (TensorProduct.prodRight ℂ ℂ V3 V2 V3)))))

end
end Physics.LiSixQuarkBlockCoordinates
