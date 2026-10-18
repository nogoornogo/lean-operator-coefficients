import Math.RepresentationTheory.ExteriorSquareCompression
import Mathlib.Algebra.Algebra.Equiv

/-! Matrix similarity, double commutators and actual exterior action.
No particle, gauge group or mass eigenvalue is assumed. -/
set_option autoImplicit false
namespace Math.ExteriorSquareTransport
noncomputable section
open ExteriorSquareCoordinates
variable {n : ℕ} (T : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))

def conjugate : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  Matrix.toLinAlgEquiv'.trans ((T.conjAlgEquiv ℂ).trans Matrix.toLinAlgEquiv'.symm)

theorem toLin_conjugate (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toLin' (conjugate T X) =
      T.toLinearMap.comp ((Matrix.toLin' X).comp T.symm.toLinearMap) := by
  change Matrix.toLinAlgEquiv' (conjugate T X) = _
  simp [conjugate, LinearEquiv.conjAlgEquiv_apply]
  rfl

def exterior : Space n ≃ₗ[ℂ] Space n :=
  LinearEquiv.ofLinearMap (exteriorPower.map 2 T.toLinearMap)
    (exteriorPower.map 2 T.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

theorem compressed_infinitesimal (X : Matrix (Fin n) (Fin n) ℂ) :
    (exterior T).symm.toLinearMap.comp
      ((infinitesimal (conjugate T X)).comp (exterior T).toLinearMap) = infinitesimal X :=
  compress_infinitesimal T.toLinearMap T.symm.toLinearMap
    (fun x => T.symm_apply_apply x) (conjugate T X) X
    (by intro x; simp [toLin_conjugate])

theorem infinitesimal_natural (X : Matrix (Fin n) (Fin n) ℂ) (x : Space n) :
    infinitesimal (conjugate T X) (exterior T x) = exterior T (infinitesimal X x) := by
  apply (exterior T).symm.injective
  simpa using DFunLike.congr_fun (compressed_infinitesimal T X) x

def doubleCommutator (B X : Matrix (Fin n) (Fin n) ℂ) :=
  B * (B * X - X * B) - (B * X - X * B) * B

theorem doubleCommutator_conjugate (B X : Matrix (Fin n) (Fin n) ℂ) :
    doubleCommutator (conjugate T B) (conjugate T X) =
      conjugate T (doubleCommutator B X) := by
  simp [doubleCommutator]

theorem eigenvector_conjugate (B X : Matrix (Fin n) (Fin n) ℂ) (g m : ℂ)
    (h : g^2 • doubleCommutator B X = m • X) :
    g^2 • doubleCommutator (conjugate T B) (conjugate T X) = m • conjugate T X := by
  rw [doubleCommutator_conjugate, ← map_smul, h, map_smul]

theorem conjugate_refl (X : Matrix (Fin n) (Fin n) ℂ) :
    conjugate (LinearEquiv.refl ℂ _) X = X := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [show Matrix.toLinAlgEquiv' _ = Matrix.toLin' _ from rfl, toLin_conjugate]
  rfl

theorem conjugate_trans (S : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    conjugate S (conjugate T X) = conjugate (T.trans S) X := by
  apply Matrix.toLinAlgEquiv'.injective
  change Matrix.toLin' _ = Matrix.toLin' _
  simp only [toLin_conjugate]
  rfl

end
end Math.ExteriorSquareTransport
