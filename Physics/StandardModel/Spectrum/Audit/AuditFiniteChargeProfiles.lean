import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.ProfileOperatorSignatures
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Math

/-! PROFILE-1 regression and negative controls. These are target-spectrum
tests, not claims of actual UV realization or physical radical support. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Finite charge-profile audit imports SU(6): {mod}"

namespace GUT.AuditFiniteChargeProfiles

noncomputable section

open FiniteChargeProfiles StandardBranchProtonObstruction
open StandardAbelianCharge StandardModelLocalOperator FiniteAbelianChargeSectors

/-- Actual circle-valued characters of a finite cyclic residual group. -/
def cyclicLabels (n : ℕ) [NeZero n] :
    ZMod n →+ ChargeLabel (Multiplicative (ZMod n)) where
  toFun r := Additive.ofMul
    { toFun := fun x => ZMod.toCircle (r * x.toAdd)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [mul_add, AddChar.map_add_eq_mul] }
  map_zero' := by
    apply Additive.toMul.injective
    ext x
    simp
  map_add' r s := by
    apply Additive.toMul.injective
    ext x
    simp [add_mul, AddChar.map_add_eq_mul]

theorem cyclicLabels_injective (n : ℕ) [NeZero n] :
    Function.Injective (cyclicLabels n) := by
  intro r s h
  apply ZMod.injective_toCircle
  simpa [cyclicLabels] using congrArg
    (fun q : ChargeLabel (Multiplicative (ZMod n)) => q.toMul (Multiplicative.ofAdd 1)) h

theorem order_two_character :
    cyclicLabels 2 1 ≠ 0 ∧ (2 : ℕ) • cyclicLabels 2 1 = 0 := by
  constructor
  · intro h
    have := (cyclicLabels_injective 2) (h.trans (map_zero (cyclicLabels 2)).symm)
    norm_num at this
  · rw [← map_nsmul, show (2 : ℕ) • (1 : ZMod 2) = 0 by decide, map_zero]

theorem order_three_character :
    cyclicLabels 3 1 ≠ 0 ∧ (3 : ℕ) • cyclicLabels 3 1 = 0 := by
  constructor
  · intro h
    have := (cyclicLabels_injective 3) (h.trans (map_zero (cyclicLabels 3)).symm)
    norm_num at this
  · rw [← map_nsmul, show (3 : ℕ) • (1 : ZMod 3) = 0 by decide, map_zero]

/-- Two neutral generations and one charged generation in the ten, with
three repeated charged generations in the anti-five. -/
def mixedFamily {A : Type*} [AddCommGroup A] (q : A) : Family A where
  profiles :=
    { quark := Finsupp.single 0 2 + Finsupp.single q 1
      up := Finsupp.single 0 2 + Finsupp.single q 1
      down := Finsupp.single q 3
      lepton := Finsupp.single q 3
      electron := Finsupp.single 0 2 + Finsupp.single q 1 }
  generations := 3
  positive := by decide
  totals := by constructor <;> simp

theorem mixed_compatible {A : Type*} [AddCommGroup A] (q : A) :
    OrbitCompatible (mixedFamily q).profiles := ⟨rfl, rfl, rfl⟩

theorem mixed_distinct_occupied {A : Type*} [AddCommGroup A] (q : A) (hq : q ≠ 0) :
    (mixedFamily q).profiles.quark 0 = 2 ∧
      (mixedFamily q).profiles.quark q = 1 ∧
      (mixedFamily q).profiles.down q = 3 := by
  simp [mixedFamily, hq, Ne.symm hq]

theorem mixed_distributions_differ {A : Type*} [AddCommGroup A] (q : A) (hq : q ≠ 0) :
    (mixedFamily q).profiles.quark ≠ (mixedFamily q).profiles.down := by
  intro h
  have := congrArg (fun p : A →₀ ℕ => p 0) h
  simp [mixedFamily, hq] at this

theorem cyclic_supported_signatures (n : ℕ) [NeZero n]
    (s : ChargeLabel (Multiplicative (ZMod n)) →₀ ℤ) :
    ∃ Q D : SupportedInvariantOperator
        (targetWithSinglets (mixedFamily (cyclicLabels n 1)).profiles s),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges :=
  exists_supported_signature_pair _ (mixed_compatible _) s

example : (mixedFamily (cyclicLabels 2 1)).profiles.quark 0 = 2 ∧
    (mixedFamily (cyclicLabels 2 1)).profiles.quark (cyclicLabels 2 1) = 1 ∧
    (mixedFamily (cyclicLabels 2 1)).profiles.down (cyclicLabels 2 1) = 3 :=
  mixed_distinct_occupied _ order_two_character.1

example : (mixedFamily (cyclicLabels 3 1)).profiles.quark 0 = 2 ∧
    (mixedFamily (cyclicLabels 3 1)).profiles.quark (cyclicLabels 3 1) = 1 ∧
    (mixedFamily (cyclicLabels 3 1)).profiles.down (cyclicLabels 3 1) = 3 :=
  mixed_distinct_occupied _ order_three_character.1

theorem zero_total_excluded {A : Type*} (F : Family A) : F.generations ≠ 0 :=
  F.generations_ne_zero

def incompatibleCharges {A : Type*} [AddCommGroup A] (q : A) : Charges A :=
  ⟨0, q, 0, 0, 0⟩

def incompatibleFamily {A : Type*} [AddCommGroup A] (q : A) : Family A :=
  ⟨pure 1 (incompatibleCharges q), 1, by decide, pure_totals _ _⟩

theorem incompatible_forgetting {A : Type*} [AddCommGroup A] (q : A) :
    forgetCharges (target (incompatibleFamily q).profiles) = unchargedTarget 1 :=
  forgetCharges_target (incompatibleFamily q).totals

theorem incompatible_not_orbitCompatible {A : Type*} [AddCommGroup A]
    (q : A) (hq : q ≠ 0) : ¬ OrbitCompatible (incompatibleFamily q).profiles := by
  intro h
  have := congrArg (fun p : A →₀ ℕ => p 0) h.1
  simp [incompatibleFamily, FiniteChargeProfiles.pure, incompatibleCharges, hq] at this

/-- Even with one occupied charge per species and the correct total, neither
signature need be neutral. This is not claimed to be a realizable UV source. -/
theorem incompatible_no_neutral_choice {A : Type*} [AddCommGroup A]
    (q : A) (hq : q ≠ 0) :
    ∀ k, Occupied (incompatibleFamily q).profiles k →
      protonFirst k ≠ 0 ∧ protonSecond k ≠ 0 := by
  intro k hk
  have he := (occupied_pure_iff 1 (by decide) (incompatibleCharges q) k).mp hk
  subst k
  simp [incompatibleCharges, protonFirst, protonSecond, hq]

theorem finite_residual_negative_control :
    ∀ k, Occupied (incompatibleFamily (cyclicLabels 3 1)).profiles k →
      protonFirst k ≠ 0 ∧ protonSecond k ≠ 0 :=
  incompatible_no_neutral_choice _ order_three_character.1

#print axioms integral_injective
#print axioms targetWithSinglets_apply_smReducedWeight
#print axioms targetWithSinglets_quarkProfile
#print axioms targetWithSinglets_upProfile
#print axioms targetWithSinglets_downProfile
#print axioms targetWithSinglets_leptonProfile
#print axioms targetWithSinglets_electronProfile
#print axioms forgetCharges_targetWithSinglets
#print axioms targetWithSinglets_pure
#print axioms occupied_pure_iff
#print axioms exists_occupied_compatible
#print axioms exists_occupied_neutral
#print axioms exists_occupied_trivial_characters
#print axioms exists_supported_signature_pair
#print axioms cyclicLabels_injective
#print axioms order_two_character
#print axioms order_three_character
#print axioms mixed_distinct_occupied
#print axioms mixed_distributions_differ
#print axioms cyclic_supported_signatures
#print axioms zero_total_excluded
#print axioms incompatible_forgetting
#print axioms incompatible_not_orbitCompatible
#print axioms incompatible_no_neutral_choice
#print axioms finite_residual_negative_control

end

end GUT.AuditFiniteChargeProfiles
