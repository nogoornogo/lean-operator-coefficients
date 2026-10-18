import GUT.E6.Minuscule.SU5Coordinates
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Actual exterior and dual actions behind the SU(5) block matrices

The exterior-square infinitesimal action is constructed by polarizing the
actual exterior-power functor. Its entries, not just its weights or dimension,
are the `wedgeMatrix` used in the E6 coordinate comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open GUT.SU5
open scoped Matrix

def pairOrder (p : Pair) : Fin 2 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![p.val.1, p.val.2] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p.property])

def pairOrderEquiv : Pair ≃ (Fin 2 ↪o Fin 5) where
  toFun := pairOrder
  invFun p := ⟨(p 0, p 1), p.strictMono (by decide)⟩
  left_inv p := by rfl
  right_inv p := by ext i; fin_cases i <;> rfl

def pairSetEquiv : Pair ≃ Set.powersetCard (Fin 5) 2 :=
  pairOrderEquiv.trans Set.powersetCard.ofFinEmbEquiv

noncomputable section

def exteriorBasis : Module.Basis Pair ℂ Matter.Ten :=
  UnitaryMatter.tenBasis.reindex pairSetEquiv.symm

def exteriorMatrix (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix Pair Pair ℂ :=
  LinearMap.toMatrix exteriorBasis exteriorBasis (exteriorPower.map 2 (Matrix.toLin' X))

theorem exteriorMatrix_minor (X : Matrix (Fin 5) (Fin 5) ℂ) (a b : Pair) :
    exteriorMatrix X a b =
      X a.val.1 b.val.1 * X a.val.2 b.val.2 - X a.val.1 b.val.2 * X a.val.2 b.val.1 := by
  rw [exteriorMatrix, LinearMap.toMatrix_apply]
  simp only [exteriorBasis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_symm, UnitaryMatter.tenBasis]
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_fin_two]
  simp [UnitaryMatter.fiveBasis, pairSetEquiv, Matrix.toLin'_apply]
  change X a.val.1 b.val.1 * X a.val.2 b.val.2 -
    X a.val.2 b.val.1 * X a.val.1 b.val.2 = _
  ring

/-- Polarization of the actual exterior functor; this is not an assumed matrix action. -/
def exteriorInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ) : Module.End ℂ Matter.Ten :=
  exteriorPower.map 2 (LinearMap.id + Matrix.toLin' X) - LinearMap.id -
    exteriorPower.map 2 (Matrix.toLin' X)

theorem exteriorMatrix_one : exteriorMatrix (1 : Matrix (Fin 5) (Fin 5) ℂ) = 1 := by
  simp [exteriorMatrix]

theorem exteriorInfinitesimal_matrix (X : Matrix (Fin 5) (Fin 5) ℂ) :
    LinearMap.toMatrix exteriorBasis exteriorBasis (exteriorInfinitesimal X) =
      wedgeMatrix X := by
  have h : LinearMap.id + Matrix.toLin' X = Matrix.toLin' (1 + X) := by simp
  rw [exteriorInfinitesimal, h,
    map_sub (LinearMap.toMatrix exteriorBasis exteriorBasis),
    map_sub (LinearMap.toMatrix exteriorBasis exteriorBasis), LinearMap.toMatrix_id]
  change exteriorMatrix (1 + X) - 1 - exteriorMatrix X = wedgeMatrix X
  rw [← exteriorMatrix_one]
  ext a b
  simp only [Matrix.sub_apply, exteriorMatrix_minor, Matrix.add_apply, Matrix.one_apply,
    wedgeMatrix]
  ring

theorem exteriorMatrix_firstOrder (X : Matrix (Fin 5) (Fin 5) ℂ) (t : ℂ) :
    exteriorMatrix (1 + t • X) = 1 + t • wedgeMatrix X + t ^ 2 • exteriorMatrix X := by
  rw [← exteriorMatrix_one]
  ext a b
  simp only [exteriorMatrix_minor, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, wedgeMatrix]
  ring

def dualInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ) : Module.End ℂ Matter.BarFive :=
  -Module.Dual.transpose (Matrix.toLin' X)

theorem dualInfinitesimal_matrix (X : Matrix (Fin 5) (Fin 5) ℂ) :
    LinearMap.toMatrix UnitaryMatter.barFiveBasis UnitaryMatter.barFiveBasis
      (dualInfinitesimal X) = -X.transpose := by
  rw [dualInfinitesimal,
    map_neg (LinearMap.toMatrix UnitaryMatter.barFiveBasis UnitaryMatter.barFiveBasis)]
  simp [UnitaryMatter.barFiveBasis, UnitaryMatter.fiveBasis]

theorem dualInfinitesimal_pairing (X : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Matter.BarFive) (v : Matter.Five) :
    dualInfinitesimal X f v + f (Matrix.toLin' X v) = 0 := by
  simp [dualInfinitesimal, Module.Dual.transpose_apply]

theorem matter_ten_matrix (g : StandardModelEmbedding.TargetGroup) :
    LinearMap.toMatrix exteriorBasis exteriorBasis (Matter.ten g) =
      exteriorMatrix g.val := rfl

theorem matter_barFive_matrix (g : StandardModelEmbedding.TargetGroup) :
    LinearMap.toMatrix UnitaryMatter.barFiveBasis UnitaryMatter.barFiveBasis
      (Matter.antifundamental g) = (g⁻¹).val.transpose := by
  change LinearMap.toMatrix UnitaryMatter.fiveBasis.dualBasis
    UnitaryMatter.fiveBasis.dualBasis
    (Module.Dual.transpose (Matrix.toLin' (g⁻¹).val)) = _
  simp [UnitaryMatter.fiveBasis]

private def wedge (u v : Matter.Five) : Matter.Ten := exteriorPower.ιMulti ℂ 2 ![u, v]

private theorem wedge_add_left (u v w : Matter.Five) :
    wedge (u + v) w = wedge u w + wedge v w :=
  (exteriorPower.ιMulti ℂ 2).map_vecCons_add _ _ _

private theorem wedge_add_right (u v w : Matter.Five) :
    wedge u (v + w) = wedge u v + wedge u w := by
  have upd (z : Matter.Five) : Function.update ![u, 0] (Fin.succ 0) z = ![u, z] := by
    ext i
    fin_cases i <;> simp
  simpa only [upd, wedge] using
    (exteriorPower.ιMulti ℂ 2).map_update_add ![u, 0] (Fin.succ 0) v w

/-- The actual functor polarization satisfies the usual exterior Leibniz rule. -/
theorem exteriorInfinitesimal_leibniz (X : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Matter.Five) :
    exteriorInfinitesimal X (exteriorPower.ιMulti ℂ 2 ![u, v]) =
      exteriorPower.ιMulti ℂ 2 ![Matrix.toLin' X u, v] +
      exteriorPower.ιMulti ℂ 2 ![u, Matrix.toLin' X v] := by
  simp only [exteriorInfinitesimal, LinearMap.sub_apply, LinearMap.id_apply,
    exteriorPower.map_apply_ιMulti]
  change wedge (u + Matrix.toLin' X u) (v + Matrix.toLin' X v) -
    wedge u v - wedge (Matrix.toLin' X u) (Matrix.toLin' X v) = _
  rw [wedge_add_left, wedge_add_right, wedge_add_right]
  change _ = wedge (Matrix.toLin' X u) v + wedge u (Matrix.toLin' X v)
  abel

end

end GUT.E6.Minuscule.SU5Coordinates
