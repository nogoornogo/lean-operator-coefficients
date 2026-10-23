import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Matrix coefficients and first derivatives of the actual exterior-square
functor, in any finite dimension. No group or particle species is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.ExteriorSquareCoordinates
noncomputable section

variable {n : ℕ}

abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Space (n : ℕ) := ⋀[ℂ]^2 (Fin n → ℂ)

def pairOrder (p : Pair n) : Fin 2 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![p.val.1, p.val.2] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p.property])

def pairOrderEquiv : Pair n ≃ (Fin 2 ↪o Fin n) where
  toFun := pairOrder
  invFun p := ⟨(p 0, p 1), p.strictMono (by decide)⟩
  left_inv p := by rfl
  right_inv p := by ext i; fin_cases i <;> rfl

def pairSetEquiv : Pair n ≃ Set.powersetCard (Fin n) 2 :=
  pairOrderEquiv.trans Set.powersetCard.ofFinEmbEquiv

def basis : Module.Basis (Pair n) ℂ (Space n) :=
  ((Pi.basisFun ℂ (Fin n)).exteriorPower 2).reindex pairSetEquiv.symm

theorem basis_apply (p : Pair n) :
    basis p = exteriorPower.ιMulti ℂ 2
      ![Pi.single p.val.1 1, Pi.single p.val.2 1] := by
  simp only [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  congr 1
  ext i j
  fin_cases i <;> simp [pairSetEquiv, pairOrderEquiv, Pi.basisFun_apply] <;> rfl

def matrix (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Pair n) (Pair n) ℂ :=
  LinearMap.toMatrix basis basis (exteriorPower.map 2 (Matrix.toLin' M))

theorem matrix_minor (M : Matrix (Fin n) (Fin n) ℂ) (a b : Pair n) :
    matrix M a b =
      M a.val.1 b.val.1 * M a.val.2 b.val.2 -
        M a.val.1 b.val.2 * M a.val.2 b.val.1 := by
  rw [matrix, LinearMap.toMatrix_apply]
  simp only [basis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_symm]
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_fin_two]
  simp [pairSetEquiv, Matrix.toLin'_apply]
  change M a.val.1 b.val.1 * M a.val.2 b.val.2 -
    M a.val.2 b.val.1 * M a.val.1 b.val.2 = _
  ring

def tangent (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Pair n) (Pair n) ℂ := fun a b =>
  X a.val.1 b.val.1 * (if a.val.2 = b.val.2 then 1 else 0) +
  (if a.val.1 = b.val.1 then 1 else 0) * X a.val.2 b.val.2 -
  (X a.val.1 b.val.2 * (if a.val.2 = b.val.1 then 1 else 0) +
   (if a.val.1 = b.val.2 then 1 else 0) * X a.val.2 b.val.1)

/-! Polarization constructs the infinitesimal map on the same carrier. -/

def infinitesimal (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Space n) :=
  exteriorPower.map 2 (LinearMap.id + Matrix.toLin' X) - LinearMap.id -
    exteriorPower.map 2 (Matrix.toLin' X)

private def wedge (u v : Fin n → ℂ) : Space n := exteriorPower.ιMulti ℂ 2 ![u, v]

private theorem wedge_add_left (u v w : Fin n → ℂ) :
    wedge (u + v) w = wedge u w + wedge v w :=
  (exteriorPower.ιMulti ℂ 2).map_vecCons_add _ _ _

private theorem wedge_add_right (u v w : Fin n → ℂ) :
    wedge u (v + w) = wedge u v + wedge u w := by
  have upd (z : Fin n → ℂ) : Function.update ![u, 0] (Fin.succ 0) z = ![u, z] := by
    ext i
    fin_cases i <;> simp
  simpa only [upd, wedge] using
    (exteriorPower.ιMulti ℂ 2).map_update_add ![u, 0] (Fin.succ 0) v w

theorem infinitesimal_leibniz (X : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    infinitesimal X (exteriorPower.ιMulti ℂ 2 ![u, v]) =
      exteriorPower.ιMulti ℂ 2 ![Matrix.toLin' X u, v] +
      exteriorPower.ιMulti ℂ 2 ![u, Matrix.toLin' X v] := by
  simp only [infinitesimal, LinearMap.sub_apply, LinearMap.id_apply,
    exteriorPower.map_apply_ιMulti]
  change wedge (u + Matrix.toLin' X u) (v + Matrix.toLin' X v) -
    wedge u v - wedge (Matrix.toLin' X u) (Matrix.toLin' X v) = _
  rw [wedge_add_left, wedge_add_right, wedge_add_right]
  change _ = wedge (Matrix.toLin' X u) v + wedge u (Matrix.toLin' X v)
  abel

theorem infinitesimal_matrix (X : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.toMatrix basis basis (infinitesimal X) = tangent X := by
  let L : Module.End ℂ (Space n) ≃ₗ[ℂ] Matrix (Pair n) (Pair n) ℂ :=
    LinearMap.toMatrix basis basis
  change L (infinitesimal X) = tangent X
  have h : LinearMap.id + Matrix.toLin' X = Matrix.toLin' (1 + X) := by simp
  rw [infinitesimal, h, map_sub L, map_sub L]
  have h1 : L LinearMap.id = matrix (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp [L, matrix]
  rw [h1]
  change matrix (1 + X) - matrix 1 - matrix X = tangent X
  ext a b
  simp only [Matrix.sub_apply, matrix_minor, Matrix.add_apply, Matrix.one_apply, tangent]
  ring

local instance : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup

theorem hasDerivAt_matrix {M : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (X i j) t)
    (h0 : M t = 1) (a b : Pair n) :
    HasDerivAt (fun s => matrix (M s) a b) (tangent X a b) t := by
  simp_rw [matrix_minor]
  convert! ((h a.val.1 b.val.1).mul (h a.val.2 b.val.2)).sub
      ((h a.val.1 b.val.2).mul (h a.val.2 b.val.1)) using 1
  simp [h0, tangent, Matrix.one_apply]

end
end Math.ExteriorSquareCoordinates
