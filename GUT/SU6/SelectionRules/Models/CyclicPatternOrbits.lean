import GUT.SU6.SelectionRules.Models.CyclicPatternSearch

namespace GUT.SU6CyclicPatternOrbits
set_option autoImplicit false
open GUT.SU6CyclicPatternSearch
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem charge_rescaling (k x y h : ZMod 5) :
    qque (k*x) (k*y) (k*h) = k * qque x y h ∧
    llhh (k*y) (k*h) = k * llhh y h := by
  constructor <;> simp only [qque, llhh] <;> ring

theorem tests_invariant (k x y h : ZMod 5) (hk : k ≠ 0) :
    (qque (k*x) (k*y) (k*h) ≠ 0 ∧ llhh (k*y) (k*h) = 0) ↔
      qque x y h ≠ 0 ∧ llhh y h = 0 := by
  rw [(charge_rescaling k x y h).1, (charge_rescaling k x y h).2]
  simp [mul_eq_zero, hk]

theorem normalized_charge (x y h : ZMod 5) (hq : qque x y h ≠ 0) :
    qque ((qque x y h)⁻¹*x) ((qque x y h)⁻¹*y) ((qque x y h)⁻¹*h) = 1 := by
  rw [(charge_rescaling _ x y h).1]
  exact inv_mul_cancel₀ hq

/-- Hypercharge dressing: 6Y charges of Q,L,H are 1,-3,3. -/
theorem hypercharge_dressing (s x y h : ZMod 5) :
    qque (x+s) (y-3*s) (h+3*s) = qque x y h ∧
    llhh (y-3*s) (h+3*s) = llhh y h := by
  constructor <;> simp only [qque, llhh] <;> ring

/-- Pointwise fifteen phases; no assumption that the factors are characters. -/
theorem scalar_block_neutral (a c w : ZMod 5) :
    2*(a+c+w)-(a+2*c)-(a+2*w) = 0 := by ring

theorem no_scalar_block_fit (x y h a c w : ZMod 5)
    (hq : qque x y h ≠ 0) :
    ¬ (x = a+c+w ∧ -x-h = a+2*c ∧ -y+h = a+2*w) := by
  rintro ⟨hQ,hU,hE⟩
  apply hq
  unfold qque
  rw [hU,hE,hQ]
  exact scalar_block_neutral a c w

end GUT.SU6CyclicPatternOrbits
