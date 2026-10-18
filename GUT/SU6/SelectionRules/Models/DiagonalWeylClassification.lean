import GUT.SU6.Characters.WeylMatrix
import Math.LinearAlgebra.Matrix.DiagonalWeylStabilizer

/-! Diagonal-vacuum classification for supplied phase/permutation SU(6)
representatives. No classification of all SU(6) automorphisms is assumed. -/
namespace GUT.DiagonalWeylClassification
set_option autoImplicit false
noncomputable section
open Math.DiagonalWeylStabilizer
abbrev SU6 := Matrix.specialUnitaryGroup (Fin 6) ℂ
abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ

/-- The SU(6) inverse is the conjugate transpose, so the matrix classification
applies to every supplied representative of the indicated form. -/
theorem fixed_iff (w : SU6) (s : Equiv.Perm (Fin 6)) (u : Fin 6 → Circle)
    (hw : (w : Matrix6) = representative s u) (d : Fin 6 → ℂ) :
    (w : Matrix6) * Matrix.diagonal d * ((w⁻¹ : SU6) : Matrix6) =
      Matrix.diagonal d ↔ ∀ i, d (s i) = d i := by
  change (w : Matrix6) * Matrix.diagonal d * star (w : Matrix6) = _ ↔ _
  rw [hw]
  exact Math.DiagonalWeylStabilizer.fixed_iff s u d

/-- All supplied SU(6) Weyl representatives preserving a nondegenerate 5+1
split fix its singled-out coordinate. The other five may be permuted. -/
theorem split_fixed_iff (w : SU6) (s : Equiv.Perm (Fin 6)) (u : Fin 6 → Circle)
    (hw : (w : Matrix6) = representative s u) (a b : ℂ) (hab : a ≠ b) :
    let d : Fin 6 → ℂ := fun i => if i = WeylMatrix.i6 then b else a
    (w : Matrix6) * Matrix.diagonal d * ((w⁻¹ : SU6) : Matrix6) =
      Matrix.diagonal d ↔ s WeylMatrix.i6 = WeylMatrix.i6 := by
  dsimp only
  rw [fixed_iff w s u hw]
  exact split_preserves_iff s WeylMatrix.i6 a b hab
end
end GUT.DiagonalWeylClassification
