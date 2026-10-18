import Physics.StandardModel.Operators.HeeckLeSixQuarkExtraction
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Matrix presentations of the constructed source orbits and the symbolic
extraction map. Inverse identities follow from uniform reconstruction, never
from reducing a supplied product of evaluated matrices. -/
namespace GUT.HeeckLeSixQuarkMatrix
noncomputable section
open LiSixQuarkLocalAction Matrix
variable {K : Type*} [Field K] [CharZero K]
attribute [local irreducible] HeeckLeSixQuarkRecipe.orbit

def flatten : Arr (K := K) ≃ₗ[K] (Fin 25 → K) where
  toFun c i := c ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
    ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2
  invFun v p q := v ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q))
  left_inv c := by ext p q; simp
  right_inv v := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def basis : Matrix (Fin 25) (Fin 25) K := fun i j =>
  HeeckLeSixQuarkRecipe.orbit j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
    ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2

def inverse : Matrix (Fin 25) (Fin 25) K :=
  LinearMap.toMatrix' (HeeckLeSixQuarkExtraction.extraction.comp flatten.symm.toLinearMap)

omit [CharZero K] in
theorem forward_mulVec (v : Fin 25 → K) :
    flatten.symm (basis *ᵥ v) = HeeckLeSixQuarkExtraction.rawAssembly v := by
  ext p q
  change (∑ j : Fin 25, basis ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q)) j*v j) =
    (∑ j : Fin 25, v j • HeeckLeSixQuarkRecipe.orbit j) p q
  simp only [basis, Equiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem left_inverse : inverse (K := K)*basis = 1 := by
  have hv (v : Fin 25 → K) : inverse *ᵥ (basis *ᵥ v) = v := by
    rw [inverse, LinearMap.toMatrix'_mulVec]
    change HeeckLeSixQuarkExtraction.extraction (flatten.symm (basis *ᵥ v)) = v
    rw [forward_mulVec, HeeckLeSixQuarkExtraction.extraction_rawAssembly]
  ext i j
  have h := congrFun (hv (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
  simpa [Matrix.one_apply, Pi.single_apply] using h

theorem right_inverse : basis (K := K)*inverse = 1 := mul_eq_one_comm.mp left_inverse

end
end GUT.HeeckLeSixQuarkMatrix
