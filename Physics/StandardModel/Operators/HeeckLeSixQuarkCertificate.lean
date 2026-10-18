import Physics.StandardModel.Operators.HeeckLeSixQuarkConvention
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! An exact rational change-of-basis certificate for 25 selected orbit vectors.
The two literal sources and their words construct the forward matrix. The
inverse is derived by quotient/pair reconstruction and five scalar equations. -/
namespace GUT.HeeckLeSixQuarkCertificate
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient
open Matrix

def basisMatrix : Matrix (Fin 25) (Fin 25) ℂ := basisRational.map (Rat.castHom ℂ)
def inverseMatrix : Matrix (Fin 25) (Fin 25) ℂ := inverseRational.map (Rat.castHom ℂ)

theorem left_inverse : inverseMatrix * basisMatrix = 1 := by
  rw [basisMatrix, inverseMatrix, ← Matrix.map_mul, rational_left_inverse]
  simp
theorem right_inverse : basisMatrix * inverseMatrix = 1 := by
  rw [basisMatrix, inverseMatrix, ← Matrix.map_mul, rational_right_inverse]
  simp

def matrixEquiv : (Fin 25 → ℂ) ≃ₗ[ℂ] (Fin 25 → ℂ) :=
  { basisMatrix.mulVecLin with
    invFun := inverseMatrix.mulVec
    left_inv := by
      intro v
      change inverseMatrix *ᵥ (basisMatrix *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, left_inverse, Matrix.one_mulVec]
    right_inv := by
      intro v
      change basisMatrix *ᵥ (inverseMatrix *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, right_inverse, Matrix.one_mulVec] }

def flatten : (Fin 5 → Fin 5 → ℂ) ≃ₗ[ℂ] (Fin 25 → ℂ) where
  toFun c i := c ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
    ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2
  invFun v p q := v ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25) (p,q))
  left_inv c := by ext p q; simp
  right_inv v := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem orbitArray_agrees (i j : Fin 25) :
    flatten (orbitArray j) i = basisMatrix i j := by
  have he := congrArg (fun x : ℚ => (x : ℂ)) (orbitR_agrees i j)
  change orbitArray j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
      ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2 = (basisRational i j : ℂ)
  unfold orbitArray seedCoordinates
  rw [LiSixQuarkCertificate.wordR_cast]
  exact he

/-- Assembly from orbit coordinates into the independent color/Weyl coordinates. -/
def coordinateEquiv : (Fin 25 → ℂ) ≃ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) :=
  matrixEquiv.trans flatten.symm

theorem assemble_extract (c : Fin 5 → Fin 5 → ℂ) :
    coordinateEquiv (coordinateEquiv.symm c) = c := coordinateEquiv.apply_symm_apply c

theorem extract_assemble (v : Fin 25 → ℂ) :
    coordinateEquiv.symm (coordinateEquiv v) = v := coordinateEquiv.symm_apply_apply v

end
end GUT.HeeckLeSixQuarkCertificate
