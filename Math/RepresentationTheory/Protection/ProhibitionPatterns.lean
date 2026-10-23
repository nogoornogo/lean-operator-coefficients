import Math.RepresentationTheory.Protection.ProhibitionInput

/-! Concrete cyclic output of the scalar necessity criterion. -/
namespace Math.ProhibitionPatterns
set_option autoImplicit false
noncomputable section
open Representation SelectionCriteria
variable {k : ℕ} [NeZero k] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem cyclic_forbidden_iff [Nontrivial V]
    (r : Representation ℂ (CyclicCharge.Group k) V) (q : ZMod k)
    (hs : ∀ g v, r g v = MixedChargeSelection.cyclicCharacter g q • v) :
    Forbidden (IntertwiningMap r (trivial ℂ (CyclicCharge.Group k) ℂ)) ↔ q ≠ 0 := by
  rw [ScalarProhibitionNecessity.forbidden_iff_detect r
    (fun g => MixedChargeSelection.cyclicCharacter g q) hs,
    MixedChargeSelection.cyclic_detect_iff]

theorem cyclic_neutral_allowed [Nontrivial V]
    (r : Representation ℂ (CyclicCharge.Group k) V)
    (hs : ∀ g v, r g v = MixedChargeSelection.cyclicCharacter g (0 : ZMod k) • v) :
    Allowed (IntertwiningMap r (trivial ℂ (CyclicCharge.Group k) ℂ)) := by
  have h := cyclic_forbidden_iff r 0 hs
  rw [forbidden_iff_not_allowed] at h
  classical
  by_contra hn
  exact (h.mp hn) rfl
end
end Math.ProhibitionPatterns
