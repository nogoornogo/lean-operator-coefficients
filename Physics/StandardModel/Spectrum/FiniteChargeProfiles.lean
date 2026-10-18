import Physics.StandardModel.Spectrum.FiniteSMTarget
import Physics.StandardModel.Operators.AbelianProtonCharacter

open Math

/-!
# Finite, family-dependent SM charge profiles

Natural multiplicities describe oriented matter; integer coefficients describe
its virtual character. Equal species totals do not imply equal distributions.
The neutrality result here is conditional coefficient algebra, not a theorem
about actual mass-radical vectors or dynamical operator coefficients.
-/

open scoped BigOperators

namespace GUT.FiniteChargeProfiles

noncomputable section

open StandardBranchProtonObstruction StandardAbelianCharge StandardSMCharacterTarget

variable {A : Type*}

/-- One nonnegative finite multiplicity distribution for each left-handed species. -/
abbrev Profiles (A : Type*) := Charges (A →₀ ℕ)

def total (p : A →₀ ℕ) : ℕ := p.sum fun _ n => n

@[simp] theorem total_zero : total (0 : A →₀ ℕ) = 0 := by simp [total]

@[simp] theorem total_single (q : A) (n : ℕ) :
    total (Finsupp.single q n) = n := by simp [total]

@[simp] theorem total_add (p r : A →₀ ℕ) :
    total (p + r) = total p + total r := by
  exact Finsupp.sum_add_index' (by simp) (by simp)

theorem exists_positive_of_total_pos (p : A →₀ ℕ) (h : 0 < total p) :
    ∃ q, 0 < p q := by
  by_contra hn
  have hz : p = 0 := by
    ext q
    simpa using (not_exists.mp hn q)
  simp [hz] at h

/-- A shared number of generations, with no equality of charge profiles. -/
structure HasCommonTotal (P : Profiles A) (N : ℕ) : Prop where
  quark : total P.quark = N
  up : total P.up = N
  down : total P.down = N
  lepton : total P.lepton = N
  electron : total P.electron = N

/-- The positive-orientation family target. Singlet index data is independent. -/
structure Family (A : Type*) where
  profiles : Profiles A
  generations : ℕ
  positive : 0 < generations
  totals : HasCommonTotal profiles generations

theorem Family.generations_ne_zero (F : Family A) : F.generations ≠ 0 :=
  Nat.ne_of_gt F.positive

def pure (N : ℕ) (k : Charges A) : Profiles A :=
  ⟨Finsupp.single k.quark N, Finsupp.single k.up N,
    Finsupp.single k.down N, Finsupp.single k.lepton N,
    Finsupp.single k.electron N⟩

theorem pure_totals (N : ℕ) (k : Charges A) : HasCommonTotal (pure N k) N := by
  constructor <;> simp [pure]

/-- Natural multiplicities embedded into the virtual-index coefficient ring. -/
def integral (p : A →₀ ℕ) : A →₀ ℤ := Finsupp.mapRange Nat.cast (by simp) p

@[simp] theorem integral_apply (p : A →₀ ℕ) (q : A) :
    integral p q = (p q : ℤ) := rfl

@[simp] theorem integral_single (q : A) (n : ℕ) :
    integral (Finsupp.single q n) = Finsupp.single q (n : ℤ) :=
  Finsupp.mapRange_single

theorem integral_injective : Function.Injective (integral (A := A)) := by
  intro p r h
  ext q
  exact Int.ofNat_inj.mp (congrArg (fun f : A →₀ ℤ => f q) h)

def atWeight (w : ReducedWeight) (p : A →₀ ℕ) : ResolvedCharacter A :=
  Finsupp.mapDomain (fun q => (w, q)) (integral p)

@[simp] theorem atWeight_apply (w v : ReducedWeight) (p : A →₀ ℕ) (q : A) :
    atWeight w p (v, q) = if v = w then (p q : ℤ) else 0 := by
  classical
  by_cases h : v = w
  · subst v
    simp [atWeight, Finsupp.mapDomain_apply_of_injective (fun _ _ h => (Prod.mk.inj h).2)]
  · rw [ite_eq_right h, atWeight, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨r, hr⟩
    exact h (congrArg Prod.fst hr).symm

/-- Each weight of a species receives that species' entire charge distribution. -/
def target (P : Profiles A) : ResolvedCharacter A :=
  ∑ i : Fin 15, atWeight (smReducedWeight i) (smCharge P i)

def targetWithSinglets (P : Profiles A) (singlets : A →₀ ℤ) : ResolvedCharacter A :=
  target P + singletResolvedCharacter singlets

theorem target_apply_smReducedWeight (P : Profiles A) (i : Fin 15) (q : A) :
    target P (smReducedWeight i, q) = (smCharge P i q : ℤ) := by
  classical
  simp [target, Finsupp.finsetSum_apply, smReducedWeight_inj]

theorem targetWithSinglets_apply_smReducedWeight (P : Profiles A) (s : A →₀ ℤ)
    (i : Fin 15) (q : A) :
    targetWithSinglets P s (smReducedWeight i, q) = (smCharge P i q : ℤ) := by
  simp [targetWithSinglets, target_apply_smReducedWeight,
    singletResolvedCharacter_apply_of_weight_ne_zero s (smReducedWeight_nonzero i)]

@[simp] theorem target_quarkProfile (P : Profiles A) :
    quarkProfile (target P) = integral P.quark := by
  classical
  ext q
  simp [quarkProfile, target, smCharge, Finsupp.finsetSum_apply]

@[simp] theorem target_upProfile (P : Profiles A) :
    upProfile (target P) = integral P.up := by
  classical
  ext q
  simp [upProfile, target, smCharge, Finsupp.finsetSum_apply]

@[simp] theorem target_downProfile (P : Profiles A) :
    downProfile (target P) = integral P.down := by
  classical
  ext q
  simp [downProfile, target, smCharge, Finsupp.finsetSum_apply]

@[simp] theorem target_leptonProfile (P : Profiles A) :
    leptonProfile (target P) = integral P.lepton := by
  classical
  ext q
  simp [leptonProfile, target, smCharge, Finsupp.finsetSum_apply]

@[simp] theorem target_electronProfile (P : Profiles A) :
    electronProfile (target P) = integral P.electron := by
  classical
  ext q
  simp [electronProfile, target, smCharge, Finsupp.finsetSum_apply]

theorem chargeProfile_targetWithSinglets (P : Profiles A) (s : A →₀ ℤ)
    {w : ReducedWeight} (hw : w ≠ 0) :
    chargeProfile (targetWithSinglets P s) w = chargeProfile (target P) w := by
  ext q
  simp [targetWithSinglets, singletResolvedCharacter_apply_of_weight_ne_zero s hw]

@[simp] theorem targetWithSinglets_quarkProfile (P : Profiles A) (s : A →₀ ℤ) :
    quarkProfile (targetWithSinglets P s) = integral P.quark := by
  rw [quarkProfile, chargeProfile_targetWithSinglets P s reducedTenQ_ne_zero]
  exact target_quarkProfile P

@[simp] theorem targetWithSinglets_upProfile (P : Profiles A) (s : A →₀ ℤ) :
    upProfile (targetWithSinglets P s) = integral P.up := by
  rw [upProfile, chargeProfile_targetWithSinglets P s reducedTenUp_ne_zero]
  exact target_upProfile P

@[simp] theorem targetWithSinglets_downProfile (P : Profiles A) (s : A →₀ ℤ) :
    downProfile (targetWithSinglets P s) = integral P.down := by
  rw [downProfile, chargeProfile_targetWithSinglets P s reducedBarFiveDown_ne_zero]
  exact target_downProfile P

@[simp] theorem targetWithSinglets_leptonProfile (P : Profiles A) (s : A →₀ ℤ) :
    leptonProfile (targetWithSinglets P s) = integral P.lepton := by
  rw [leptonProfile, chargeProfile_targetWithSinglets P s reducedBarFiveLepton_ne_zero]
  exact target_leptonProfile P

@[simp] theorem targetWithSinglets_electronProfile (P : Profiles A) (s : A →₀ ℤ) :
    electronProfile (targetWithSinglets P s) = integral P.electron := by
  rw [electronProfile, chargeProfile_targetWithSinglets P s reducedTenElectron_ne_zero]
  exact target_electronProfile P

/-- Forget labels by summing collisions, not by evaluating at a selected charge. -/
def forgetCharges (p : ResolvedCharacter A) : ReducedWeight →₀ ℤ :=
  Finsupp.mapDomain Prod.fst p

theorem forgetCharges_atWeight (w : ReducedWeight) (p : A →₀ ℕ) :
    forgetCharges (atWeight w p) = Finsupp.single w (total p : ℤ) := by
  classical
  simp only [forgetCharges, atWeight, ← Finsupp.mapDomain_comp]
  change (integral p).sum (fun _ n => Finsupp.single w n) = _
  rw [integral, Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, total, Nat.cast_sum]
  exact (Finsupp.single_sum _ _ _).symm

def unchargedTarget (N : ℕ) : ReducedWeight →₀ ℤ :=
  ∑ i : Fin 15, Finsupp.single (smReducedWeight i) (N : ℤ)

theorem HasCommonTotal.smCharge {P : Profiles A} {N : ℕ}
    (h : HasCommonTotal P N) (i : Fin 15) : total (smCharge P i) = N := by
  fin_cases i <;> simp [StandardSMCharacterTarget.smCharge,
    h.quark, h.up, h.down, h.lepton, h.electron]

theorem forgetCharges_target {P : Profiles A} {N : ℕ} (h : HasCommonTotal P N) :
    forgetCharges (target P) = unchargedTarget N := by
  simp only [forgetCharges, target, Finsupp.mapDomain_finsetSum]
  change (∑ i : Fin 15, forgetCharges (atWeight (smReducedWeight i) (smCharge P i))) = _
  simp [forgetCharges_atWeight, h.smCharge, unchargedTarget]

theorem forgetCharges_singlets (s : A →₀ ℤ) :
    forgetCharges (singletResolvedCharacter s) =
      Finsupp.single 0 (s.sum fun _ n => n) := by
  classical
  simp only [forgetCharges, singletResolvedCharacter, ← Finsupp.mapDomain_comp]
  change s.sum (fun _ n => Finsupp.single 0 n) = _
  exact (Finsupp.single_sum _ _ _).symm

theorem forgetCharges_targetWithSinglets {P : Profiles A} {N : ℕ}
    (h : HasCommonTotal P N) (s : A →₀ ℤ) :
    forgetCharges (targetWithSinglets P s) =
      unchargedTarget N + Finsupp.single 0 (s.sum fun _ n => n) := by
  rw [targetWithSinglets, forgetCharges, Finsupp.mapDomain_add]
  exact congrArg₂ (· + ·) (forgetCharges_target h) (forgetCharges_singlets s)

@[simp] theorem target_pure (N : ℕ) (k : Charges A) :
    target (pure N k) = exactSMResolvedCharacter (N : ℤ) k := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  have h : smCharge (pure N k) i = Finsupp.single (smCharge k i) N := by
    fin_cases i <;> rfl
  simp [h, atWeight, smResolvedKey]

@[simp] theorem targetWithSinglets_pure (N : ℕ) (k : Charges A) (s : A →₀ ℤ) :
    targetWithSinglets (pure N k) s =
      exactSMWithSingletsResolvedCharacter (N : ℤ) k s := by
  simp [targetWithSinglets, exactSMWithSingletsResolvedCharacter]

/-- Additional orbit equalities, not part of `Family`. -/
def OrbitCompatible (P : Profiles A) : Prop :=
  P.quark = P.up ∧ P.quark = P.electron ∧ P.down = P.lepton

/-- Positive occupation of each selected oriented species. -/
def Occupied (P : Profiles A) (k : Charges A) : Prop :=
  0 < P.quark k.quark ∧ 0 < P.up k.up ∧ 0 < P.down k.down ∧
    0 < P.lepton k.lepton ∧ 0 < P.electron k.electron

theorem occupied_iff_supported (P : Profiles A) (k : Charges A) :
    Occupied P k ↔ ChargesSupported (target P) k := by
  simp [Occupied, ChargesSupported, Nat.pos_iff_ne_zero]

theorem occupied_iff_supported_withSinglets (P : Profiles A) (s : A →₀ ℤ)
    (k : Charges A) :
    Occupied P k ↔ ChargesSupported (targetWithSinglets P s) k := by
  simp [Occupied, ChargesSupported, Nat.pos_iff_ne_zero]

theorem occupied_pure_iff (N : ℕ) (hN : 0 < N) (k l : Charges A) :
    Occupied (pure N k) l ↔ l = k := by
  classical
  simp only [Occupied, pure, Finsupp.single_apply]
  constructor
  · rintro ⟨hQ, hu, hd, hL, he⟩
    have eq_of_pos (a b : A) (h : 0 < if a = b then N else 0) : b = a := by
      split_ifs at h with hab
      · exact hab.symm
      · omega
    exact Charges.ext (eq_of_pos _ _ hQ) (eq_of_pos _ _ hu)
      (eq_of_pos _ _ hd) (eq_of_pos _ _ hL) (eq_of_pos _ _ he)
  · rintro rfl
    simp [hN]

/-- The two orbit totals need only be positive, not equal. -/
theorem exists_occupied_compatible_of_positive_totals [AddCommGroup A] (P : Profiles A)
    (hQ : 0 < total P.quark) (hD : 0 < total P.down) (h : OrbitCompatible P) :
    ∃ k, Occupied P k ∧ SU5OrbitCompatible k := by
  obtain ⟨q, hq⟩ := exists_positive_of_total_pos P.quark hQ
  obtain ⟨r, hr⟩ := exists_positive_of_total_pos P.down hD
  refine ⟨sectorCharges q r, ?_, sectorCharges_su5OrbitCompatible q r⟩
  exact ⟨hq, h.1 ▸ hq, hr, h.2.2 ▸ hr, h.2.1 ▸ hq⟩

theorem exists_occupied_compatible [AddCommGroup A] (F : Family A)
    (h : OrbitCompatible F.profiles) :
    ∃ k, Occupied F.profiles k ∧ SU5OrbitCompatible k :=
  exists_occupied_compatible_of_positive_totals F.profiles
    (F.totals.quark ▸ F.positive) (F.totals.down ▸ F.positive) h

theorem exists_occupied_neutral [AddCommGroup A] (F : Family A)
    (h : OrbitCompatible F.profiles) :
    ∃ k, Occupied F.profiles k ∧ protonFirst k = 0 ∧ protonSecond k = 0 := by
  obtain ⟨k, hk, hc⟩ := exists_occupied_compatible F h
  exact ⟨k, hk, proton_functionals_eq_zero_of_su5OrbitCompatible k hc⟩

/-- Physical residual charges are characters of `H`, not elements of `H`. -/
theorem exists_occupied_trivial_characters_of_positive_totals {H : Type*} [CommGroup H]
    (P : Profiles (FiniteAbelianChargeSectors.ChargeLabel H))
    (hQ : 0 < total P.quark) (hD : 0 < total P.down) (h : OrbitCompatible P) :
    ∃ k, Occupied P k ∧
      FiniteAbelianChargeSectors.protonFirstCharacter k = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter k = 1 := by
  obtain ⟨k, hk, hc⟩ := exists_occupied_compatible_of_positive_totals P hQ hD h
  exact ⟨k, hk, FiniteAbelianChargeSectors.protonCharacters_eq_one_of_su5OrbitCompatible k hc⟩

theorem exists_occupied_trivial_characters {H : Type*} [CommGroup H]
    (F : Family (FiniteAbelianChargeSectors.ChargeLabel H))
    (h : OrbitCompatible F.profiles) :
    ∃ k, Occupied F.profiles k ∧
      FiniteAbelianChargeSectors.protonFirstCharacter k = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter k = 1 :=
  exists_occupied_trivial_characters_of_positive_totals F.profiles
    (F.totals.quark ▸ F.positive) (F.totals.down ▸ F.positive) h

end

end GUT.FiniteChargeProfiles
