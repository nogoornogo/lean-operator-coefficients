import Math.LinearAlgebra.ConstrainedCompleteness

/-! Algebraic prohibition/permission. No generation mechanism is supplied. -/
namespace Math.SelectionCriteria
set_option autoImplicit false

def Allowed (C : Type*) [Zero C] : Prop := ∃ c : C, c ≠ 0
def Forbidden (C : Type*) [Zero C] : Prop := ∀ c : C, c = 0

theorem forbidden_iff_not_allowed (C : Type*) [Zero C] :
    Forbidden C ↔ ¬ Allowed C := by
  simp only [Forbidden, Allowed, not_exists, not_not]

variable {k C R : Type*} [Semiring k] [AddCommMonoid C] [Module k C]
  [AddCommMonoid R] [Module k R]

structure Certificate (C R : Type*) [Zero C] [Zero R] : Prop where
  allowed : Allowed C ↔ Allowed R
  forbidden : Forbidden C ↔ Forbidden R

theorem allowed_equiv (e : C ≃ₗ[k] R) : Allowed C ↔ Allowed R := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨e x, fun h => hx (e.map_eq_zero_iff.mp h)⟩
  · rintro ⟨x,hx⟩
    exact ⟨e.symm x, fun h => hx (e.symm.map_eq_zero_iff.mp h)⟩

theorem ofEquiv (e : C ≃ₗ[k] R) : Certificate C R where
  allowed := allowed_equiv e
  forbidden := by
    rw [forbidden_iff_not_allowed, forbidden_iff_not_allowed]
    exact not_congr (allowed_equiv e)

theorem forbidden_family {I : Type*} (C : I → Type*) [∀ i, Zero (C i)] :
    Forbidden (∀ i, C i) ↔ ∀ i, Forbidden (C i) := by
  constructor
  · intro h i x
    classical
    have hi := congrFun (h (Function.update (fun j => (0 : C j)) i x)) i
    simpa using hi
  · intro h f
    funext i
    exact h i (f i)

theorem allowed_family {I : Type*} (C : I → Type*) [∀ i, Zero (C i)] :
    Allowed (∀ i, C i) ↔ ∃ i, Allowed (C i) := by
  rw [← not_iff_not, ← forbidden_iff_not_allowed, not_exists]
  simp_rw [← forbidden_iff_not_allowed]
  exact forbidden_family C

theorem forbidden_prod (A B : Type*) [Zero A] [Zero B] :
    Forbidden (A × B) ↔ Forbidden A ∧ Forbidden B := by
  constructor
  · intro h
    exact ⟨fun a => congrArg Prod.fst (h (a, 0)),
      fun b => congrArg Prod.snd (h (0, b))⟩
  · rintro ⟨ha, hb⟩ ⟨a,b⟩
    exact Prod.ext (ha a) (hb b)

end Math.SelectionCriteria
