import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.LiSixQuarkOrbitData
import Physics.StandardModel.Operators.LiSixQuarkBlockExtraction
import Physics.StandardModel.Operators.LiSixQuarkReducedSeeds
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An exact rational change-of-basis certificate for 25 selected orbit vectors.
The forward columns retain their literal-contraction identification. Extraction
is derived by symbolic reconstruction in 4-, 6-, 6- and 9-dimensional blocks. -/
namespace GUT.LiSixQuarkCertificate
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient LiSixQuarkConvention
open Matrix

def orbitArray (j : Fin 25) : Fin 5 → Fin 5 → ℂ :=
  (selectedWord j).foldl (fun c g => transform c g) (seedCoordinates (selectedSeed j))

def basisMatrix : Matrix (Fin 25) (Fin 25) ℂ := basisRational.map (Rat.castHom ℂ)
/-- The inverse is induced by the explicit small-block extraction map,
not supplied as a dense table of rational entries. -/
def inverseMatrix : Matrix (Fin 25) (Fin 25) ℂ :=
  LinearMap.toMatrix' LiSixQuarkBlockExtraction.extraction

theorem left_inverse : inverseMatrix * basisMatrix = 1 := by
  have hv (v : Fin 25 → ℂ) : inverseMatrix *ᵥ (basisMatrix *ᵥ v) = v := by
    rw [inverseMatrix, LinearMap.toMatrix'_mulVec]
    change LiSixQuarkBlockExtraction.decode
      (LiSixQuarkBlockAssembly.entries
        (LiSixQuarkBlockExtraction.reindex (basisMatrix *ᵥ v))) = v
    have ha : LiSixQuarkBlockExtraction.reindex (basisMatrix *ᵥ v) =
        LiSixQuarkBlockAssembly.originalAssembly v := rfl
    rw [ha]
    exact LiSixQuarkBlockExtraction.decode_original v
  ext i j
  have h := congrFun (hv (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
  simpa [Matrix.one_apply, Pi.single_apply] using h

/-- In finite square dimension, the left inverse already gives the right
inverse. No second rational matrix-product certificate is needed here. -/
theorem right_inverse : basisMatrix * inverseMatrix = 1 := by
  exact mul_eq_one_comm.mp left_inverse

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

theorem colorMatrixR_cast (g : Fin 4) (p q : Fin 5) :
    (colorMatrixR g p q : ℂ) = colorMatrix g p q := by
  fin_cases g <;> fin_cases p <;> fin_cases q <;> norm_num [colorMatrixR, colorMatrix]
theorem spinMatrixR_cast (g : Fin 4) (p q : Fin 5) :
    (spinMatrixR g p q : ℂ) = spinMatrix g p q := by
  fin_cases g <;> fin_cases p <;> fin_cases q <;> norm_num [spinMatrixR, spinMatrix]

theorem transformR_cast (c : Fin 5 → Fin 5 → ℚ) (g : Fin 4) :
    transform (fun p q => (c p q : ℂ)) g = fun p q => (transformR c g p q : ℂ) := by
  rw [← LiSixQuarkLocalAction.action_actual]
  exact (LiSixQuarkSeedRecipe.map_action (Rat.castHom ℂ) g c).symm

theorem wordR_cast (w : List (Fin 4)) (c : Fin 5 → Fin 5 → ℚ) :
    w.foldl (fun c g => transform c g) (fun p q => (c p q : ℂ)) =
      fun p q => (w.foldl transformR c p q : ℂ) := by
  induction w generalizing c with
  | nil => rfl
  | cons g w ih =>
    change w.foldl (fun c g => transform c g) (transform (fun p q => (c p q : ℂ)) g) = _
    rw [transformR_cast]
    exact ih _

theorem orbitArray_agrees (i j : Fin 25) :
    flatten (orbitArray j) i = basisMatrix i j := by
  have he := congrArg (fun x : ℚ => (x : ℂ)) (orbitR_agrees i j)
  change orbitArray j ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).1
      ((finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).symm i).2 = (basisRational i j : ℂ)
  unfold orbitArray seedCoordinates
  rw [wordR_cast]
  exact he

/-- Assembly from orbit coordinates into the independent color/Weyl coordinates. -/
def coordinateEquiv : (Fin 25 → ℂ) ≃ₗ[ℂ] (Fin 5 → Fin 5 → ℂ) :=
  matrixEquiv.trans flatten.symm

theorem assemble_extract (c : Fin 5 → Fin 5 → ℂ) :
    coordinateEquiv (coordinateEquiv.symm c) = c := coordinateEquiv.apply_symm_apply c

theorem extract_assemble (v : Fin 25 → ℂ) :
    coordinateEquiv.symm (coordinateEquiv v) = v := coordinateEquiv.symm_apply_apply v

theorem printed_probe_zero (k : Fin 10) :
    LiSixQuarkExtension.extraProbe (seedCoordinates k.castSucc) = 0 := by
  change LiSixQuarkExtension.extraProbe
    (fun p q => (LiSixQuarkSeedRecipe.projected (K := ℚ) k.castSucc p q : ℂ)) = 0
  rw [LiSixQuarkSeedRecipe.rational_cast]
  exact LiSixQuarkReducedSeeds.printed_probe_zero k


/-- Every word in the actual within-species generators still lies in the
separating probe's kernel for each of the ten printed seeds. -/
theorem printed_orbit_probe_zero (k : Fin 10) (w : List (Fin 4)) :
    LiSixQuarkExtension.extraProbe
      (w.foldl (fun c g => transform c g) (seedCoordinates k.castSucc)) = 0 :=
  LiSixQuarkExtension.extraProbe_word _ w (printed_probe_zero k)

theorem extra_outside_printed_span :
    LiSixQuarkExtension.extra ∉ Submodule.span ℂ
      {c | ∃ (k : Fin 10) (w : List (Fin 4)),
        c = w.foldl (fun c g => transform c g) (seedCoordinates k.castSucc)} := by
  intro h
  have hk : Submodule.span ℂ
      {c | ∃ (k : Fin 10) (w : List (Fin 4)),
        c = w.foldl (fun c g => transform c g) (seedCoordinates k.castSucc)} ≤
      LinearMap.ker LiSixQuarkExtension.extraProbeLinear := by
    apply Submodule.span_le.mpr
    rintro c ⟨k,w,rfl⟩
    exact printed_orbit_probe_zero k w
  have he := hk h
  change LiSixQuarkExtension.extraProbe LiSixQuarkExtension.extra = 0 at he
  rw [LiSixQuarkExtension.extraProbe_extra] at he
  exact one_ne_zero he

end
end GUT.LiSixQuarkCertificate
