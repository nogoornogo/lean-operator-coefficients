import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic

/-! Odd elements of an exterior algebra anticommute, including inhomogeneous
odd polynomials. Their squares vanish in characteristic different from two. -/
namespace Math.ExteriorOdd
set_option autoImplicit false
noncomputable section
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
abbrev A := ExteriorAlgebra k V

def Odd (x : A (k := k) (V := V)) : Prop := CliffordAlgebra.involute x = -x

theorem generator_slide (v : V) (x : A (k := k) (V := V)) :
    ExteriorAlgebra.ι k v*x = CliffordAlgebra.involute x*ExteriorAlgebra.ι k v := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
    simp only [CliffordAlgebra.involute.commutes]
    exact (Algebra.commutes a (ExteriorAlgebra.ι k v)).symm
  | ι w =>
    simp only [CliffordAlgebra.involute_ι, neg_mul]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w)
  | mul x y hx hy =>
    rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, ← map_mul]
  | add x y hx hy => simp only [mul_add, map_add, add_mul, hx, hy]

theorem even_central (x : A (k := k) (V := V))
    (hx : CliffordAlgebra.involute x = x) (y : A (k := k) (V := V)) : x*y = y*x := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap a => exact (Algebra.commutes a x).symm
  | ι v =>
    have h := generator_slide v x
    rw [hx] at h
    exact h.symm
  | mul y z hy hz => rw [← mul_assoc, hy, mul_assoc, hz, ← mul_assoc]
  | add y z hy hz => simp only [mul_add, add_mul, hy, hz]

theorem odd_slide (x : A (k := k) (V := V)) (hx : Odd x) (y : A (k := k) (V := V)) :
    x*y = CliffordAlgebra.involute y*x := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap a =>
    simp only [CliffordAlgebra.involute.commutes]
    exact (Algebra.commutes a x).symm
  | ι v =>
    have h := generator_slide v x
    rw [hx, neg_mul] at h
    simp only [CliffordAlgebra.involute_ι, neg_mul]
    simpa using congrArg Neg.neg h.symm
  | mul y z hy hz => rw [← mul_assoc, hy, mul_assoc, hz, ← mul_assoc, ← map_mul]
  | add y z hy hz => simp only [mul_add, map_add, add_mul, hy, hz]

theorem anticommute (x y : A (k := k) (V := V)) (hx : Odd x) (hy : Odd y) :
    x*y = -(y*x) := by rw [odd_slide x hx, hy, neg_mul]

theorem square_zero [NeZero (2 : k)] (x : A (k := k) (V := V)) (hx : Odd x) : x*x = 0 := by
  have h := anticommute x x hx hx
  have h2 : (2 : k) • (x*x) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne _)

end
end Math.ExteriorOdd
