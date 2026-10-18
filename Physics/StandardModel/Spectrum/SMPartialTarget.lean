import Physics.StandardModel.Spectrum.ProfileChiralIndex

/-! Local SM dual-index information. Other weight coefficients are not fixed;
the condition concerns the dual difference, not the complete light spectrum. -/

set_option autoImplicit false
namespace GUT.SMPartialTarget
noncomputable section
open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles StandardBranchProtonObstruction

variable {A : Type*} [AddCommGroup A]

def MatchesSM (p : ResolvedCharacter A) (P : Profiles A) : Prop :=
  ∀ (i : Fin 15) (q : A), chiralDifference p (smReducedWeight i, q) = (smCharge P i q : ℤ)

theorem of_full_target (p : ResolvedCharacter A) (P : Profiles A) (s : A →₀ ℤ)
    (ht : chiralDifference p = chiralDifference (targetWithSinglets P s)) : MatchesSM p P := by
  intro i q
  rw [ht]
  exact chiralDifference_target_apply P s i q

theorem profile_eq (p : ResolvedCharacter A) (P : Profiles A) (ht : MatchesSM p P)
    (i : Fin 15) : chargeProfile (chiralDifference p) (smReducedWeight i) = integral (smCharge P i) := by
  ext q
  exact ht i q

theorem coefficient_lower_bound (p : ResolvedCharacter A) (P : Profiles A)
    (hn : ∀ key, 0 ≤ p key) (ht : MatchesSM p P) (i : Fin 15) (q : A) :
    (smCharge P i q : ℤ) ≤ p (smReducedWeight i, q) := by
  have he := ht i q
  have hp := hn (-(smReducedWeight i, q))
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply] at he
  omega

theorem chargesSupported_of_occupied (p : ResolvedCharacter A) (P : Profiles A)
    (hn : ∀ key, 0 ≤ p key) (ht : MatchesSM p P)
    (k : Charges A) (hk : Occupied P k) : ChargesSupported p k := by
  have h (i : Fin 15) : p (smResolvedKey k i) ≠ 0 := by
    have hp := coefficient_lower_bound p P hn ht i (smCharge k i)
    have hq := smCharge_pos_of_occupied P k hk i
    change p (smReducedWeight i, smCharge k i) ≠ 0
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [quarkProfile, smResolvedKey, smCharge, (smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] using h 0
  · simpa [upProfile, smResolvedKey, smCharge, (smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] using h 8
  · simpa [downProfile, smResolvedKey, smCharge, (smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] using h 9
  · simpa [leptonProfile, smResolvedKey, smCharge, (smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] using h 13
  · simpa [electronProfile, smResolvedKey, smCharge, (smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] using h 14

/-- Added sectors may have nonzero dual index elsewhere. -/
theorem add_of_dual_vanishes (p r : ResolvedCharacter A) (P : Profiles A)
    (ht : MatchesSM p P) (hr : ∀ (i : Fin 15) (q : A),
      chiralDifference r (smReducedWeight i, q) = 0) : MatchesSM (p + r) P := by
  intro i q
  have he := ht i q
  have hz := hr i q
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply, Finsupp.add_apply] at *
  omega

end
end GUT.SMPartialTarget
