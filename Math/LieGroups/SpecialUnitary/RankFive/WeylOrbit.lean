import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Charge-resolved standard SU(5) Weyl orbits

This is the permutation algebra of five raw exponents, with no ambient
SU(6) group. It does not assert faithful evaluation on the SU(5) torus:
common diagonal shifts become trivial there. The rank-four normal form and
independent charge labels are supplied by ChargeResolved.

This file proves the coefficient-level content of the standard-branch orbit
argument.  In every fixed residual shift, the representative weights for
`Q`, `u^c`, and `e^c` in the `10` have equal coefficients, and the
representative weights for `d^c` and `L` in the anti-fundamental have equal
coefficients, for every Weyl-invariant normalized Laurent polynomial.
-/

namespace Math
namespace StandardSU5Orbit

noncomputable section

abbrev Weight := Fin 5 → ℤ
abbrev Poly := Weight →₀ ℤ

/-- Permute an exponent vector so that coordinate `i` moves to coordinate
`sigma i`. -/
def permuteWeight (sigma : Equiv.Perm (Fin 5)) (e : Weight) : Weight :=
  fun i => e (sigma.symm i)

theorem permuteWeight_injective (sigma : Equiv.Perm (Fin 5)) :
    Function.Injective (permuteWeight sigma) := by
  intro e f h
  funext i
  have hi := congrFun h (sigma i)
  simpa [permuteWeight] using hi

/-- The induced Weyl action on normalized Laurent polynomials. -/
def permute (sigma : Equiv.Perm (Fin 5)) (p : Poly) : Poly :=
  Finsupp.mapDomain (permuteWeight sigma) p

/-- Invariance under the full Weyl group of the standard `SU(5)` block. -/
def WeylInvariant (p : Poly) : Prop :=
  ∀ sigma : Equiv.Perm (Fin 5), permute sigma p = p

/-- Weyl invariance identifies coefficients at every pair of permuted
exponents. -/
theorem coeff_permute_eq (p : Poly) (h : WeylInvariant p)
    (sigma : Equiv.Perm (Fin 5)) (e : Weight) :
    p (permuteWeight sigma e) = p e := by
  have hp := congrArg (fun q : Poly => q (permuteWeight sigma e)) (h sigma)
  rw [permute, Finsupp.mapDomain_apply_of_injective (permuteWeight_injective sigma)] at hp
  exact hp.symm

/-- A single coordinate exponent. -/
def coordinate (i : Fin 5) : Weight :=
  fun j => if j = i then 1 else 0

/-- An equal power of all five coordinates, hence an `S_5`-fixed residual
charge shift. -/
def residualShift (k : ℤ) : Weight :=
  fun _ => k

theorem permuteWeight_add (sigma : Equiv.Perm (Fin 5)) (e f : Weight) :
    permuteWeight sigma (e + f) =
      permuteWeight sigma e + permuteWeight sigma f := by
  rfl

theorem permuteWeight_neg (sigma : Equiv.Perm (Fin 5)) (e : Weight) :
    permuteWeight sigma (-e) = -permuteWeight sigma e := by
  rfl

@[simp]
theorem permuteWeight_residualShift (sigma : Equiv.Perm (Fin 5)) (k : ℤ) :
    permuteWeight sigma (residualShift k) = residualShift k := by
  rfl

@[simp]
theorem permuteWeight_coordinate (sigma : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permuteWeight sigma (coordinate i) = coordinate (sigma i) := by
  funext j
  simp [permuteWeight, coordinate, Equiv.symm_apply_eq]

/-!
## Representatives of the Standard Model weight orbits
-/

/-- A representative color-weak weight in the `10`. -/
def tenQ (k : ℤ) : Weight :=
  residualShift k + coordinate 0 + coordinate 3

/-- A representative color-color weight in the `10`. -/
def tenUp (k : ℤ) : Weight :=
  residualShift k + coordinate 0 + coordinate 1

/-- The weak-weak weight in the `10`. -/
def tenElectron (k : ℤ) : Weight :=
  residualShift k + coordinate 3 + coordinate 4

/-- A representative inverse-color weight in the anti-fundamental. -/
def barFiveDown (k : ℤ) : Weight :=
  residualShift k - coordinate 0

/-- A representative inverse-weak weight in the anti-fundamental. -/
def barFiveLepton (k : ℤ) : Weight :=
  residualShift k - coordinate 3

theorem permuteWeight_swap31_tenQ (k : ℤ) :
    permuteWeight (Equiv.swap (3 : Fin 5) 1) (tenQ k) = tenUp k := by
  ext i
  fin_cases i <;>
    simp [permuteWeight, tenQ, tenUp, residualShift, coordinate,
      Equiv.swap_apply_of_ne_of_ne]

theorem permuteWeight_swap04_tenQ (k : ℤ) :
    permuteWeight (Equiv.swap (0 : Fin 5) 4) (tenQ k) =
      tenElectron k := by
  ext i
  fin_cases i <;>
    simp [permuteWeight, tenQ, tenElectron, residualShift, coordinate,
      Equiv.swap_apply_of_ne_of_ne]

theorem permuteWeight_swap03_barFiveDown (k : ℤ) :
    permuteWeight (Equiv.swap (0 : Fin 5) 3) (barFiveDown k) =
      barFiveLepton k := by
  ext i
  fin_cases i <;>
    simp [permuteWeight, barFiveDown, barFiveLepton, residualShift, coordinate,
      Equiv.swap_apply_of_ne_of_ne]

/-- At every residual shift, the three `10` weight representatives have equal
coefficients in a Weyl-invariant normalized Laurent polynomial. -/
theorem ten_coefficients_equal (p : Poly) (h : WeylInvariant p) (k : ℤ) :
    p (tenQ k) = p (tenUp k) ∧
      p (tenQ k) = p (tenElectron k) := by
  constructor
  · have hp := coeff_permute_eq p h
      (Equiv.swap (3 : Fin 5) 1) (tenQ k)
    rw [permuteWeight_swap31_tenQ] at hp
    exact hp.symm
  · have hp := coeff_permute_eq p h
      (Equiv.swap (0 : Fin 5) 4) (tenQ k)
    rw [permuteWeight_swap04_tenQ] at hp
    exact hp.symm

/-- At every residual shift, the anti-fundamental color and weak weight
representatives have equal coefficients. -/
theorem barFive_coefficients_equal
    (p : Poly) (h : WeylInvariant p) (k : ℤ) :
    p (barFiveDown k) = p (barFiveLepton k) := by
  have hp := coeff_permute_eq p h
    (Equiv.swap (0 : Fin 5) 3) (barFiveDown k)
  rw [permuteWeight_swap03_barFiveDown] at hp
  exact hp.symm

end

end StandardSU5Orbit
end Math
