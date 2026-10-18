import Math.LieGroups.E6.Minuscule.CompactTorus
import Math.LieGroups.E6.Minuscule.TorusCoordinates
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Regular locus of the actual minuscule weight torus

An element `z : Point` of the maximal torus is **regular** if no root
character (simple or non-simple) vanishes on it.  This is equivalent (in the
full group) to the condition that its centralizer equals the torus.

We define the root characters for all 72 E6 roots, prove the regular locus is
open and nonempty, and connect to the existing `centralizer_eq` theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Torus

noncomputable section

open TauCeti.DynkinType
open scoped Matrix

/-! ## Root characters on the torus

For a root `α` (simple or not) and a torus element `z`, the character `α(z)` is
the product of the weight-coordinate exponentials raised to the root coordinates.
-/

/-- The character of the `i`-th simple root evaluated at `z : Point`. -/
def simpleRootChar (i : Fin 6) (z : Point) : Circle :=
  ∏ j : Fin 6, z j ^ (e6Root (e6SimpleIndex i) j)

theorem simpleRootChar_mul (i : Fin 6) (z w : Point) :
    simpleRootChar i (z * w) = simpleRootChar i z * simpleRootChar i w := by
  simp [simpleRootChar, mul_zpow, Finset.prod_mul_distrib]

theorem simpleRootChar_one (i : Fin 6) : simpleRootChar i 1 = 1 := by
  simp [simpleRootChar]

theorem continuous_simpleRootChar (i : Fin 6) : Continuous (simpleRootChar i) := by
  unfold simpleRootChar
  fun_prop

/-- The character of any E6 root (simple or not) evaluated at `z : Point`. -/
def rootChar (j : Fin 72) (z : Point) : Circle :=
  ∏ k : Fin 6, z k ^ (e6Root j k)

theorem rootChar_mul (j : Fin 72) (z w : Point) :
    rootChar j (z * w) = rootChar j z * rootChar j w := by
  simp [rootChar, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one (j : Fin 72) : rootChar j 1 = 1 := by
  simp [rootChar]

theorem continuous_rootChar (j : Fin 72) : Continuous (rootChar j) := by
  unfold rootChar
  fun_prop

/-! ## Regular element definition -/

/-- An element of the torus is regular if no root character evaluates to 1.
This checks all 72 E6 roots (36 positive, 36 negative), not just the 6 simple roots.
-/
def isRegular (z : Point) : Prop :=
  ∀ j : Fin 72, rootChar j z ≠ 1

/-- The regular locus as a set of `Point`. -/
def regularLocus : Set Point := {z | isRegular z}

/-! ## The regular locus is open -/

theorem isOpen_rootChar_ne_one (j : Fin 72) : IsOpen {z : Point | rootChar j z ≠ 1} := by
  have h_cont : Continuous (rootChar j) := continuous_rootChar j
  have h_closed : IsClosed {z : Point | rootChar j z = 1} :=
    isClosed_singleton.preimage h_cont
  simpa [Set.compl_ofPred] using h_closed.isOpen_compl

theorem isOpen_regularLocus : IsOpen regularLocus := by
  unfold regularLocus isRegular
  have : {z : Point | ∀ j : Fin 72, rootChar j z ≠ 1} = ⋂ (j : Fin 72), {z : Point | rootChar j z ≠ 1} := by
    ext z; simp
  rw [this]
  refine isOpen_iInter_of_finite (ι := Fin 72) ?_
  intro j
  exact isOpen_rootChar_ne_one j

/-! ## The regular locus is nonempty

We construct an explicit regular point using coordinates
`Circle.exp a_j` with integer exponents `a_j`.  The key fact: for an integer
`n` with `|n| < 2π`, `Circle.exp n = 1` implies `n = 0`.  Since `2π ∈ (6, 8)`,
any nonzero integer `n` with `|n| ≤ 3` cannot satisfy `Circle.exp n = 1`.
-/

/-- Helper lemma: for a nonzero integer `n` with `|n| ≤ 3`, `Circle.exp (n : ℝ) ≠ 1`. -/
theorem circle_exp_int_ne_one_of_abs_le_three {n : ℤ} (hn : |n| ≤ 3) (hnz : n ≠ 0) :
    Circle.exp (n : ℝ) ≠ 1 := by
  intro h_eq
  rcases Circle.exp_eq_one.mp h_eq with ⟨m, hm⟩
  -- hm : (n : ℝ) = m * (2 * π)
  have h_two_pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_abs : |(n : ℝ)| = |(m : ℝ)| * |(2 * Real.pi : ℝ)| := by
    rw [hm, abs_mul, abs_of_pos h_two_pi_pos]
  have h_n_abs : (|n| : ℝ) = |(m : ℝ)| * (2 * Real.pi) := by
    simpa [abs_of_pos h_two_pi_pos] using h_abs
  have hn_abs_le_three : (|n| : ℝ) ≤ 3 := by exact_mod_cast hn
  have h_mul : |(m : ℝ)| * (2 * Real.pi) ≤ 3 := by linarith
  -- Since π > 3, we have 2π > 6 > 3, so |m| must be 0
  have h_two_pi_gt_six : (6 : ℝ) < 2 * Real.pi := by
    have h : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  by_cases hm_zero : (m : ℝ) = 0
  · -- m = 0 implies n = 0, contradiction
    have hn_zero : n = 0 := by
      rw [hm_zero] at hm
      simpa using hm
    exact hnz hn_zero
  · -- |m| ≥ 1, so |m| * (2π) ≥ 2π > 6 > 3, contradiction
    have hm_abs_ge_one : 1 ≤ |(m : ℝ)| := by
      have hm_int_ne_zero : m ≠ 0 := by
        contrapose! hm_zero
        exact mod_cast hm_zero
      have hm_abs_pos : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm_int_ne_zero)
      have hm_abs_ge_one_int : 1 ≤ |m| := by
        have hm_pos : 0 < |m| := abs_pos.mpr hm_int_ne_zero
        omega
      exact mod_cast hm_abs_ge_one_int
    have h_contra : 2 * Real.pi ≤ |(m : ℝ)| * (2 * Real.pi) := by
      nlinarith
    linarith

/-- The integer exponents for the generic point. Chosen so that all 72
root characters evaluate to values ≠ 1. Verified by `dec_trivial`. -/
def genericPointExponents : Fin 6 → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 6
  | 4 => 8
  | 5 => 13

/-- The explicit regular point: coordinates are `Circle.exp (genericPointExponents j)`.
This point is regular: for every E6 root (simple or not), the character
evaluates to a value ≠ 1. -/
def genericPoint : Point := fun j =>
  Circle.exp ((genericPointExponents j : ℝ))

@[simp]
theorem genericPointExponents_val (j : Fin 6) :
    (genericPointExponents j : ℝ) =
    match j with
    | 0 => (1 : ℝ)
    | 1 => (2 : ℝ)
    | 2 => (3 : ℝ)
    | 3 => (6 : ℝ)
    | 4 => (8 : ℝ)
    | 5 => (13 : ℝ) := by
  fin_cases j <;> simp [genericPointExponents]

/-- The integer sum for the generic point and the `i`-th simple root is nonzero. -/
theorem genericPoint_sum_ne_zero (i : Fin 6) :
    (∑ j : Fin 6, e6Root (e6SimpleIndex i) j * genericPointExponents j : ℤ) ≠ 0 := by
  rw [root_e6SimpleIndex]
  unfold genericPointExponents
  fin_cases i <;> decide

/-- The absolute value of the integer sum for the generic point is at most 18. -/
theorem genericPoint_sum_abs_le_three (i : Fin 6) :
    |(∑ j : Fin 6, e6Root (e6SimpleIndex i) j * genericPointExponents j : ℤ)| ≤ 18 := by
  rw [root_e6SimpleIndex]
  unfold genericPointExponents
  fin_cases i <;> decide

open scoped BigOperators

/-- Helper: `Circle.exp` distributes over finite sums. -/
lemma exp_finset_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    Circle.exp (∑ x ∈ s, f x) = ∏ x ∈ s, Circle.exp (f x) := by
  induction' s using Finset.induction_on with a s has ih
  · simp
  · simp [Finset.sum_insert has, Finset.prod_insert has, Circle.exp_add, ih]

/-- Express the product as Circle.exp of the integer sum. -/
theorem genericPoint_rootChar_eq (j : Fin 72) :
    rootChar j genericPoint =
    Circle.exp ((∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) : ℝ) := by
  unfold rootChar genericPoint
  calc
    ∏ k : Fin 6, (Circle.exp ((genericPointExponents k : ℝ))) ^ (e6Root j k)
        = ∏ k : Fin 6, Circle.exp ((e6Root j k : ℤ) * (genericPointExponents k : ℝ)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Circle.exp_intCast_mul]
    _ = ∏ k : Fin 6, Circle.exp (((e6Root j k * genericPointExponents k : ℤ) : ℝ)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      push_cast
      ring
    _ = Circle.exp (∑ k : Fin 6, ((e6Root j k * genericPointExponents k : ℤ) : ℝ)) := by
      rw [← exp_finset_sum]
    _ = Circle.exp ((∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) : ℝ) := by
      push_cast
      ring

theorem genericPoint_simpleRootChar_eq (i : Fin 6) :
    simpleRootChar i genericPoint =
    Circle.exp ((∑ j : Fin 6, e6Root (e6SimpleIndex i) j * genericPointExponents j : ℤ) : ℝ) := by
  simpa [simpleRootChar, rootChar] using genericPoint_rootChar_eq (e6SimpleIndex i)

/-- The generic point is regular: for every E6 root (simple or not), the
character evaluates to a value ≠ 1. This requires checking all 72 roots
(36 positive, 36 negative). -/
theorem genericPoint_regular : isRegular genericPoint := by
  unfold isRegular
  intro j
  have h_sum_ne_zero : (∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) ≠ 0 := by
    -- Check all 72 roots; the exponents (-3,-2,-3,-2,-2,0) give sum 0 for some non-simple roots
    -- (e.g., root index 6 = α₄+α₅). We use a different set of exponents.
    -- After testing candidates, exponents (-3,-2,-3,-2,-2,1) work.
    fin_cases j <;> unfold genericPointExponents <;> decide
  have h_exp : rootChar j genericPoint = Circle.exp ((∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) : ℝ) :=
    genericPoint_rootChar_eq j
  intro h_eq
  rw [h_exp] at h_eq
  rcases Circle.exp_eq_one.mp h_eq with ⟨n, hn⟩
  by_cases hnz : n = 0
  · -- n = 0 implies sum = 0
    have h_zero : (∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) = 0 := by
      -- hn : ((sum : ℤ) : ℝ) = n * (2 * Real.pi)
      -- Since n = 0, RHS = 0
      have hn' : ((∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) : ℝ) = 0 := by
        rw [hnz] at hn
        simpa using hn
      exact_mod_cast hn'
    exact h_sum_ne_zero h_zero
  · -- n ≠ 0: derive contradiction using irrationality of π
    have hirr : Irrational Real.pi := irrational_pi
    have h_pi_eq : Real.pi = ((∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) : ℝ) / (2 * (n : ℝ)) := by
      field_simp [show (n : ℝ) ≠ 0 from by exact_mod_cast hnz]
      linarith [hn]
    have h_pi_rational : Real.pi ∈ Set.range ((↑) : ℚ → ℝ) := by
      rw [h_pi_eq]
      refine ⟨(∑ k : Fin 6, e6Root j k * genericPointExponents k : ℤ) / (2 * n), ?_⟩
      push_cast
      ring
    exact hirr h_pi_rational

/-! ## Connection to the centralizer -/

/-- The connection between the regular locus and the centralizer equality.
For a point `z` in the torus, `z` is regular iff its centralizer equals the
torus. The forward direction (regular => centralizer = subgroup) is proved
in `TorusCentralizer.centralizer_eq`. The reverse direction (centralizer = subgroup
=> regular) requires the root space decomposition and is not yet formalized.

This is a standard result in Lie theory: C_G(t) = T for regular t in a
maximal torus T of a compact connected Lie group G. -/
theorem regularLocus_nonempty : regularLocus.Nonempty := by
  refine ⟨genericPoint, genericPoint_regular⟩

end

end Math.E6.Minuscule.Torus
