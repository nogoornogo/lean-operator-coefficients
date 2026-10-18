import Math.LieGroups.E6.Minuscule.MatrixCommutant
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Integral coordinates for the actual minuscule weight torus.
The six selected weights are a unimodular basis, checked over integers. -/

set_option autoImplicit false

namespace Math.E6.Minuscule.Torus

open TauCeti.DynkinType
open scoped Matrix

noncomputable section

abbrev Point := Fin 6 → Circle

def powerMap {m n : Type*} [Fintype n] (M : Matrix m n ℤ) (z : n → Circle) : m → Circle :=
  fun i => ∏ j, z j ^ M i j

theorem powerMap_mul {m n p : Type*} [Fintype n] [Fintype p]
    (A : Matrix m n ℤ) (B : Matrix n p ℤ) (z : p → Circle) :
    powerMap A (powerMap B z) = powerMap (A * B) z := by
  funext i
  simp only [powerMap, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  congr 1
  funext k
  simp only [mul_comm (B _ k)]
  exact (map_sum ((zpowersHom Circle (z k)).toAdditive) _ _).symm

theorem powerMap_one {n : Type*} [Fintype n] [DecidableEq n] (z : n → Circle) :
    powerMap (1 : Matrix n n ℤ) z = z := by
  funext i
  simp [powerMap, Matrix.one_apply]

def seed : Fin 6 → Fin 27 := ![2, 3, 4, 9, 21, 23]

def seedWeights : Matrix (Fin 6) (Fin 6) ℤ := fun i => e6MinusculeWeight (seed i)

def seedInverse : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, -1, 1, 0, -1, -1;
     1, 0, 0, 0, 0, -1;
     1, -1, 1, 0, 0, -2;
     2, -1, 1, 0, 0, -2;
     1, 0, 1, 0, 0, -1;
     1, -1, 1, -1, 0, -1]

theorem seed_inverse_left : seedInverse * seedWeights = 1 := by decide +kernel
theorem seed_inverse_right : seedWeights * seedInverse = 1 := by decide +kernel

def weights (z : Point) : Fin 27 → Circle := powerMap e6MinusculeWeight z

def recover (d : Fin 27 → Circle) : Point := powerMap seedInverse (fun i => d (seed i))

theorem recover_weights (z : Point) : recover (weights z) = z := by
  change powerMap seedInverse (powerMap seedWeights z) = z
  rw [powerMap_mul, seed_inverse_left, powerMap_one]

theorem weights_recover_seed (d : Fin 27 → Circle) (i : Fin 6) :
    weights (recover d) (seed i) = d (seed i) := by
  have h := powerMap_mul seedWeights seedInverse (fun j => d (seed j))
  rw [seed_inverse_right, powerMap_one] at h
  exact congrFun h i

theorem weights_injective : Function.Injective weights :=
  Function.LeftInverse.injective recover_weights

end

end Math.E6.Minuscule.Torus
