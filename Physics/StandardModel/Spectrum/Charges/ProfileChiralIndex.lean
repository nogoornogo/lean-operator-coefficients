import Physics.StandardModel.Spectrum.Charges.FiniteChargeProfiles
import Physics.StandardModel.Spectrum.Representations.SMChiralIndex

/-!
# Positive profile coefficients in the dual SM index

Gauge-weight separation, not a torsion-free charge assumption, removes the
conjugate target at every oriented SM weight. Nonnegative actual coefficients
can then be bounded below by the natural profile multiplicities.
-/

namespace Physics.FiniteChargeProfiles

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open StandardBranchProtonObstruction

variable {A : Type*} [AddCommGroup A]

/-- Extra conjugate pairs do not alter the dual index. Their coefficients
need not vanish, so this is not an exact-spectrum assertion. -/
theorem chiralDifference_add_vectorlike (p r : ResolvedCharacter A) :
    chiralDifference (p + (r + dualCharacter r)) = chiralDifference p := by
  ext key
  simp [chiralDifference]
  ring

omit [AddCommGroup A] in
theorem targetWithSinglets_apply_neg_smWeight (P : Profiles A) (s : A →₀ ℤ)
    (i : Fin 15) (q : A) :
    targetWithSinglets P s (-smReducedWeight i, q) = 0 := by
  classical
  have hn (j : Fin 15) : -smReducedWeight i ≠ smReducedWeight j :=
    (smReducedWeight_ne_neg j i).symm
  simp [targetWithSinglets, target, hn,
    singletResolvedCharacter_apply_of_weight_ne_zero s
      (neg_ne_zero.mpr (smReducedWeight_nonzero i))]

theorem chiralDifference_target_apply (P : Profiles A) (s : A →₀ ℤ)
    (i : Fin 15) (q : A) :
    chiralDifference (targetWithSinglets P s) (smReducedWeight i, q) =
      (smCharge P i q : ℤ) := by
  simp [chiralDifference, targetWithSinglets_apply_smReducedWeight,
    targetWithSinglets_apply_neg_smWeight]

theorem chiralDifference_target_profile (P : Profiles A) (s : A →₀ ℤ)
    (i : Fin 15) :
    chargeProfile (chiralDifference (targetWithSinglets P s)) (smReducedWeight i) =
      integral (smCharge P i) := by
  ext q
  exact chiralDifference_target_apply P s i q

theorem orbitCompatible_of_dual_invariant (P : Profiles A) (s : A →₀ ℤ)
    (hi : ResolvedWeylInvariant (chiralDifference (targetWithSinglets P s))) :
    OrbitCompatible P := by
  obtain ⟨hQ, he, hd⟩ := sm_charge_profiles_equal _ hi
  have h0 := chiralDifference_target_profile P s 0
  have h8 := chiralDifference_target_profile P s 8
  have h9 := chiralDifference_target_profile P s 9
  have h13 := chiralDifference_target_profile P s 13
  have h14 := chiralDifference_target_profile P s 14
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at h0
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at h8
  rw [(smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] at h9
  rw [(smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] at h13
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at h14
  change chargeProfile _ reducedTenQ = chargeProfile _ reducedTenUp at hQ
  change chargeProfile _ reducedTenQ = chargeProfile _ reducedTenElectron at he
  change chargeProfile _ reducedBarFiveDown = chargeProfile _ reducedBarFiveLepton at hd
  rw [h0, h8] at hQ
  rw [h0, h14] at he
  rw [h9, h13] at hd
  exact ⟨integral_injective hQ, integral_injective he, integral_injective hd⟩

theorem orbitCompatible_of_dual_target (P : Profiles A) (s : A →₀ ℤ)
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (ht : chiralDifference p = chiralDifference (targetWithSinglets P s)) :
    OrbitCompatible P :=
  orbitCompatible_of_dual_invariant P s (ht ▸ chiralDifference_isWeylInvariant p hp)

theorem coefficient_lower_bound (P : Profiles A) (s : A →₀ ℤ)
    (p : ResolvedCharacter A) (hn : ∀ key, 0 ≤ p key)
    (ht : chiralDifference p = chiralDifference (targetWithSinglets P s))
    (i : Fin 15) (q : A) : (smCharge P i q : ℤ) ≤ p (smReducedWeight i, q) := by
  have he := congrArg (fun f : ResolvedCharacter A => f (smReducedWeight i, q)) ht
  rw [chiralDifference_target_apply] at he
  have hp := hn (-(smReducedWeight i, q))
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply] at he
  omega

theorem coefficient_pos (P : Profiles A) (s : A →₀ ℤ)
    (p : ResolvedCharacter A) (hn : ∀ key, 0 ≤ p key)
    (ht : chiralDifference p = chiralDifference (targetWithSinglets P s))
    (i : Fin 15) (q : A) (hq : 0 < smCharge P i q) :
    0 < p (smReducedWeight i, q) := by
  have := coefficient_lower_bound P s p hn ht i q
  omega

omit [AddCommGroup A] in
theorem smCharge_pos_of_occupied (P : Profiles A) (k : Charges A)
    (hk : Occupied P k) (i : Fin 15) : 0 < smCharge P i (smCharge k i) := by
  rcases hk with ⟨hQ, hu, hd, hL, he⟩
  fin_cases i <;> assumption

theorem chargesSupported_of_occupied (P : Profiles A) (s : A →₀ ℤ)
    (p : ResolvedCharacter A) (hn : ∀ key, 0 ≤ p key)
    (ht : chiralDifference p = chiralDifference (targetWithSinglets P s))
    (k : Charges A) (hk : Occupied P k) : ChargesSupported p k := by
  have h (i : Fin 15) := ne_of_gt (coefficient_pos P s p hn ht i _
    (smCharge_pos_of_occupied P k hk i))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [quarkProfile, smCharge, (smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] using h 0
  · simpa [upProfile, smCharge, (smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] using h 8
  · simpa [downProfile, smCharge, (smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] using h 9
  · simpa [leptonProfile, smCharge, (smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] using h 13
  · simpa [electronProfile, smCharge, (smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] using h 14

end

end Physics.FiniteChargeProfiles
