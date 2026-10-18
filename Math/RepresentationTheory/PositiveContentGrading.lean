import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Pi

/-! Positive engineering weights bound species contents uniformly in the degree. -/
namespace Math.PositiveContentGrading
set_option autoImplicit false
open scoped BigOperators
variable {S : Type*} [Fintype S] [DecidableEq S]
  (weight : S → ℕ) (positive : ∀ s, 0 < weight s)

def degree (c : S → ℕ) : ℕ := ∑ s, weight s * c s

omit [DecidableEq S] in
include positive in
theorem component_le_degree (c : S → ℕ) (s : S) : c s ≤ degree weight c := by
  have hp : 1 ≤ weight s := positive s
  have hm : c s ≤ weight s * c s := by simpa using Nat.mul_le_mul_right (c s) hp
  exact hm.trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le (weight i * c i)) (Finset.mem_univ s))

omit [DecidableEq S] in
include positive in
theorem bounded_finite (D : ℕ) : {c : S → ℕ | degree weight c ≤ D}.Finite := by
  apply (Set.Finite.pi' (fun _ : S => Set.finite_Iic D)).subset
  intro c hc s
  exact (component_le_degree weight positive c s).trans hc

def charge (q : S → ℤ) (c : S → ℕ) : ℤ := ∑ s, (c s : ℤ) * q s

omit [DecidableEq S] in
include positive in
theorem charged_bounded_finite (D : ℕ) (q : S → ℤ) (target : ℤ) :
    {c : S → ℕ | degree weight c ≤ D ∧ charge q c = target}.Finite :=
  (bounded_finite weight positive D).subset (fun _ h => h.1)

omit [DecidableEq S] in
theorem all_bounds_iff (P : (S → ℕ) → Prop) :
    (∀ D c, degree weight c ≤ D → P c) ↔ ∀ c, P c := by
  constructor
  · intro h c
    exact h (degree weight c) c le_rfl
  · intro h D c _
    exact h c

end Math.PositiveContentGrading
