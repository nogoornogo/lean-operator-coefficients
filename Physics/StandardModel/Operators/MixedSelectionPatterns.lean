import Math.LinearAlgebra.MixedSelectionRequests
import Physics.StandardModel.Operators.ProhibitionPatterns
import Physics.StandardModel.Operators.BgwChargedHiggsWeinberg

/-! Actual all-degree BGW baryon prohibition with fixed-degree LLHH allowance. -/
namespace GUT.MixedSelectionPatterns
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria MixedSelectionRequests

inductive BgwTarget where
  | bOne | bTwo | llhh
  deriving DecidableEq

/-- Baryon targets quantify all degrees; LLHH is the actual fixed (2,2) domain. -/
def bgwDomain : BgwTarget → Type
  | .bOne => ∀ n m : ℕ, ComposableBLSupport.Input
      (BgwZ6Selection.flavor (F := fun _ => ℂ))
      (BgwZ6Selection.scalarFlavor (S := fun _ => ℂ))
      (ProhibitionPatterns.target .bOne) n m
  | .bTwo => ∀ n m : ℕ, ComposableBLSupport.Input
      (BgwZ6Selection.flavor (F := fun _ => ℂ))
      (BgwZ6Selection.scalarFlavor (S := fun _ => ℂ))
      (ProhibitionPatterns.target .bTwo) n m
  | .llhh => BgwChargedHiggsWeinberg.Sector

instance (t : BgwTarget) : Zero (bgwDomain t) := by
  cases t <;> unfold bgwDomain <;> infer_instance

def bgwRequest : Request BgwTarget where
  forbid := {t | t = .bOne ∨ t = .bTwo}
  allow := {t | t = .llhh}

theorem bgw_domain_forbidden_iff (t : ProhibitionPatterns.BLTarget) :
    Forbidden (∀ n m : ℕ, ComposableBLSupport.Input
      (BgwZ6Selection.flavor (F := fun _ => ℂ))
      (BgwZ6Selection.scalarFlavor (S := fun _ => ℂ))
      (ProhibitionPatterns.target t) n m) ↔
    ProhibitionInputSM.AllForbids (BgwZ6Selection.flavor (F := fun _ => ℂ))
      (BgwZ6Selection.scalarFlavor (S := fun _ => ℂ)) (ProhibitionPatterns.target t) := by
  rw [SelectionCriteria.forbidden_family]
  simp only [SelectionCriteria.forbidden_family]

theorem bgw_satisfies : Satisfies bgwDomain bgwRequest := by
  constructor
  · intro t ht
    rcases ht with rfl | rfl
    · exact (bgw_domain_forbidden_iff .bOne).mpr
        ((ProhibitionPatterns.chosen_iff _ _ _).mp
          (ProhibitionPatterns.bgw_baryon (F := fun _ => ℂ) (S := fun _ => ℂ))
          .bOne (by change ProhibitionPatterns.BLTarget.bOne ≠ .lTwo; decide))
    · exact (bgw_domain_forbidden_iff .bTwo).mpr
        ((ProhibitionPatterns.chosen_iff _ _ _).mp
          (ProhibitionPatterns.bgw_baryon (F := fun _ => ℂ) (S := fun _ => ℂ))
          .bTwo (by change ProhibitionPatterns.BLTarget.bTwo ≠ .lTwo; decide))
  · intro t ht
    change t = .llhh at ht
    subst t
    exact BgwChargedHiggsWeinberg.exists_nonzero

theorem bgw_components : Forbidden (bgwDomain .bOne) ∧ Forbidden (bgwDomain .bTwo) ∧
    Allowed (bgwDomain .llhh) :=
  ⟨forbidden bgwDomain bgwRequest bgw_satisfies .bOne (Or.inl rfl),
   forbidden bgwDomain bgwRequest bgw_satisfies .bTwo (Or.inr rfl),
   allowed bgwDomain bgwRequest bgw_satisfies .llhh rfl⟩

/-- LFV allowance requires a nonzero selected output, not just a nonzero coefficient. -/
theorem dgt_selected_allowed (i : Fin 2) : SelectedAllowed
    (DipoleFlavorSelection.selector DgtFlavorRestriction.leptonIR
      DgtFlavorRestriction.leptonIR DgtFlavorRestriction.mu
      (DgtFlavorRestriction.targetCovector i)) := DgtFlavorRestriction.ir_dipoles_allowed i

theorem dgt_selector_range_allowed (i : Fin 2) : Allowed
    (DipoleFlavorSelection.selector DgtFlavorRestriction.leptonIR
      DgtFlavorRestriction.leptonIR DgtFlavorRestriction.mu
      (DgtFlavorRestriction.targetCovector i)).range :=
  (selected_allowed_iff_range _).mp (dgt_selected_allowed i)
end
end GUT.MixedSelectionPatterns
