import Physics.StandardModel.Spectrum.Representations.SMPartialTarget

/-! Four monitored weights for qque; opposite weights remain in the dual index. -/

set_option autoImplicit false
namespace Physics.QqueLocalTarget
noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles

def Monitored (i : Fin 15) : Prop := i = 0 ∨ i = 3 ∨ i = 8 ∨ i = 14

variable {A : Type*} [AddCommGroup A]

def Matches (p : ResolvedCharacter A) (P : Profiles A) : Prop :=
  ∀ (i : Fin 15), Monitored i → ∀ q : A,
    chiralDifference p (smReducedWeight i, q) = (smCharge P i q : ℤ)

theorem of_matchesSM (p : ResolvedCharacter A) (P : Profiles A)
    (h : SMPartialTarget.MatchesSM p P) : Matches p P := fun i _ q => h i q

theorem profile_eq (p : ResolvedCharacter A) (P : Profiles A)
    (ht : Matches p P) (i : Fin 15) (hi : Monitored i) :
    chargeProfile (chiralDifference p) (smReducedWeight i) = integral (smCharge P i) := by
  ext q
  exact ht i hi q

theorem coefficient_lower_bound (p : ResolvedCharacter A) (P : Profiles A)
    (hn : ∀ key, 0 ≤ p key) (ht : Matches p P) (i : Fin 15)
    (hi : Monitored i) (q : A) : (smCharge P i q : ℤ) ≤ p (smReducedWeight i, q) := by
  have he := ht i hi q
  have hp := hn (-(smReducedWeight i, q))
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply] at he
  omega

/-- Unmonitored species entries in the reused profile container are irrelevant. -/
theorem matches_iff_of_profiles_eq (p : ResolvedCharacter A) (P R : Profiles A)
    (hq : P.quark = R.quark) (hu : P.up = R.up) (he : P.electron = R.electron) :
    Matches p P ↔ Matches p R := by
  have hm (i : Fin 15) (hi : Monitored i) : smCharge P i = smCharge R i := by
    rcases hi with rfl | rfl | rfl | rfl
    · exact hq
    · exact hq
    · exact hu
    · exact he
  constructor <;> intro h i hi q
  · rw [← hm i hi]; exact h i hi q
  · rw [hm i hi]; exact h i hi q

theorem add_of_dual_vanishes (p r : ResolvedCharacter A) (P : Profiles A)
    (ht : Matches p P) (hr : ∀ i, Monitored i → ∀ q,
      chiralDifference r (smReducedWeight i, q) = 0) : Matches (p + r) P := by
  intro i hi q
  have he := ht i hi q
  have hz := hr i hi q
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply, Finsupp.add_apply] at *
  omega

end
end Physics.QqueLocalTarget
