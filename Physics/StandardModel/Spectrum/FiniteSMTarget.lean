import Physics.StandardModel.Spectrum.ChargeResolved

open Math

/-!
# Finite Standard Model weight targets

The fifteen oriented SM weights and independent residual charge labels are
coefficient algebra, independent of an SU(6) representation or evaluator.
The existing declaration namespace is retained for compatibility.
-/

open scoped BigOperators

namespace GUT.StandardSMCharacterTarget

noncomputable section

open StandardAbelianCharge StandardBranchProtonObstruction

def pairWeight (i j : Fin 5) : ReducedWeight :=
  normalizeWeight
    (StandardSU5Orbit.coordinate i + StandardSU5Orbit.coordinate j)

def antiWeight (i : Fin 5) : ReducedWeight :=
  normalizeWeight (-StandardSU5Orbit.coordinate i)

/-- The order agrees with `PhysicalTorusCharacterBridge.smExponent`: six
quark-doublet weights, three up-antiquark weights, three down-antiquark
weights, two lepton-doublet weights, and one positron weight. -/
def smReducedWeight : Fin 15 → ReducedWeight :=
  ![![1, 0, 0, 1],
    ![0, -1, -1, -1],
    ![0, 1, 0, 1],
    ![-1, 0, -1, -1],
    ![0, 0, 1, 1],
    ![-1, -1, 0, -1],
    ![0, 1, 1, 0],
    ![1, 0, 1, 0],
    ![1, 1, 0, 0],
    ![-1, 0, 0, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, 0],
    ![1, 1, 1, 1],
    ![0, 0, 0, -1],
    ![-1, -1, -1, 0]]

def smCharge
    {A : Type*} (k : Charges A) : Fin 15 → A :=
  ![k.quark, k.quark, k.quark, k.quark, k.quark, k.quark,
    k.up, k.up, k.up,
    k.down, k.down, k.down,
    k.lepton, k.lepton,
    k.electron]

theorem smReducedWeight_inj (i j : Fin 15) :
    smReducedWeight i = smReducedWeight j ↔ i = j := by
  revert i j
  decide

theorem smReducedWeight_nonzero (i : Fin 15) : smReducedWeight i ≠ 0 := by
  fin_cases i <;> decide

def smResolvedKey
    {A : Type*} (k : Charges A) (i : Fin 15) : ResolvedKey A :=
  (smReducedWeight i, smCharge k i)

/-- The complete fifteen-weight chiral target with arbitrary Abelian charges
on the five Standard Model multiplet types. -/
def exactSMResolvedCharacter
    {A : Type*} (generations : ℤ) (k : Charges A) :
    ResolvedCharacter A :=
  ∑ i : Fin 15, Finsupp.single (smResolvedKey k i) generations

/-- Embed an arbitrary finite virtual collection of gauge singlets.  Their
`SU(5)` weight is zero, while their residual Abelian charges are unrestricted. -/
def singletResolvedCharacter
    {A : Type*} (singlets : A →₀ ℤ) : ResolvedCharacter A :=
  Finsupp.mapDomain (fun q => ((0 : ReducedWeight), q)) singlets

/-- The exact chiral Standard Model target, allowing arbitrary gauge-singlet
matter. -/
def exactSMWithSingletsResolvedCharacter
    {A : Type*} (generations : ℤ) (k : Charges A)
    (singlets : A →₀ ℤ) : ResolvedCharacter A :=
  exactSMResolvedCharacter generations k +
    singletResolvedCharacter singlets

theorem singletResolvedCharacter_apply_of_weight_ne_zero
    {A : Type*} (singlets : A →₀ ℤ) {w : ReducedWeight} (hw : w ≠ 0)
    (q : A) :
    singletResolvedCharacter singlets (w, q) = 0 := by
  rw [singletResolvedCharacter, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨r, hr⟩
  exact hw (congrArg Prod.fst hr).symm

theorem chargeProfile_singletResolvedCharacter_of_weight_ne_zero
    {A : Type*} (singlets : A →₀ ℤ) {w : ReducedWeight} (hw : w ≠ 0) :
    chargeProfile (singletResolvedCharacter singlets) w = 0 := by
  ext q
  exact singletResolvedCharacter_apply_of_weight_ne_zero singlets hw q

theorem smReducedWeight_eq_reducedTenQ_iff (i : Fin 15) :
    smReducedWeight i = reducedTenQ ↔ i = 0 := by
  fin_cases i <;> decide

theorem smReducedWeight_eq_reducedTenUp_iff (i : Fin 15) :
    smReducedWeight i = reducedTenUp ↔ i = 8 := by
  fin_cases i <;> decide

theorem smReducedWeight_eq_reducedTenElectron_iff (i : Fin 15) :
    smReducedWeight i = reducedTenElectron ↔ i = 14 := by
  fin_cases i <;> decide

theorem smReducedWeight_eq_reducedBarFiveDown_iff (i : Fin 15) :
    smReducedWeight i = reducedBarFiveDown ↔ i = 9 := by
  fin_cases i <;> decide

theorem smReducedWeight_eq_reducedBarFiveLepton_iff (i : Fin 15) :
    smReducedWeight i = reducedBarFiveLepton ↔ i = 13 := by
  fin_cases i <;> decide

@[simp]
theorem reducedTenQ_eq_smReducedWeight_iff (i : Fin 15) :
    reducedTenQ = smReducedWeight i ↔ i = 0 := by
  rw [eq_comm]
  exact smReducedWeight_eq_reducedTenQ_iff i

@[simp]
theorem reducedTenUp_eq_smReducedWeight_iff (i : Fin 15) :
    reducedTenUp = smReducedWeight i ↔ i = 8 := by
  rw [eq_comm]
  exact smReducedWeight_eq_reducedTenUp_iff i

@[simp]
theorem reducedTenElectron_eq_smReducedWeight_iff (i : Fin 15) :
    reducedTenElectron = smReducedWeight i ↔ i = 14 := by
  rw [eq_comm]
  exact smReducedWeight_eq_reducedTenElectron_iff i

@[simp]
theorem reducedBarFiveDown_eq_smReducedWeight_iff (i : Fin 15) :
    reducedBarFiveDown = smReducedWeight i ↔ i = 9 := by
  rw [eq_comm]
  exact smReducedWeight_eq_reducedBarFiveDown_iff i

@[simp]
theorem reducedBarFiveLepton_eq_smReducedWeight_iff (i : Fin 15) :
    reducedBarFiveLepton = smReducedWeight i ↔ i = 13 := by
  rw [eq_comm]
  exact smReducedWeight_eq_reducedBarFiveLepton_iff i

theorem reducedTenQ_ne_zero : reducedTenQ ≠ 0 := by
  decide

theorem reducedTenUp_ne_zero : reducedTenUp ≠ 0 := by
  decide

theorem reducedTenElectron_ne_zero : reducedTenElectron ≠ 0 := by
  decide

theorem reducedBarFiveDown_ne_zero : reducedBarFiveDown ≠ 0 := by
  decide

theorem reducedBarFiveLepton_ne_zero : reducedBarFiveLepton ≠ 0 := by
  decide

theorem exactSMResolvedCharacter_quarkProfile
    {A : Type*} (generations : ℤ) (k : Charges A) :
    quarkProfile (exactSMResolvedCharacter generations k) =
      Finsupp.single k.quark generations := by
  classical
  ext q
  simp [quarkProfile, chargeProfile_apply, exactSMResolvedCharacter,
    smResolvedKey, smCharge, Finsupp.single_apply, ite_and, eq_comm]
  rfl

theorem exactSMResolvedCharacter_upProfile
    {A : Type*} (generations : ℤ) (k : Charges A) :
    upProfile (exactSMResolvedCharacter generations k) =
      Finsupp.single k.up generations := by
  classical
  ext q
  simp [upProfile, chargeProfile_apply, exactSMResolvedCharacter,
    smResolvedKey, smCharge, Finsupp.single_apply, ite_and, eq_comm]
  rfl

theorem exactSMResolvedCharacter_downProfile
    {A : Type*} (generations : ℤ) (k : Charges A) :
    downProfile (exactSMResolvedCharacter generations k) =
      Finsupp.single k.down generations := by
  classical
  ext q
  simp [downProfile, chargeProfile_apply, exactSMResolvedCharacter,
    smResolvedKey, smCharge, Finsupp.single_apply, ite_and, eq_comm]
  rfl

theorem exactSMResolvedCharacter_leptonProfile
    {A : Type*} (generations : ℤ) (k : Charges A) :
    leptonProfile (exactSMResolvedCharacter generations k) =
      Finsupp.single k.lepton generations := by
  classical
  ext q
  simp [leptonProfile, chargeProfile_apply, exactSMResolvedCharacter,
    smResolvedKey, smCharge, Finsupp.single_apply, ite_and, eq_comm]
  rfl

theorem exactSMResolvedCharacter_electronProfile
    {A : Type*} (generations : ℤ) (k : Charges A) :
    electronProfile (exactSMResolvedCharacter generations k) =
      Finsupp.single k.electron generations := by
  classical
  ext q
  simp [electronProfile, chargeProfile_apply, exactSMResolvedCharacter,
    smResolvedKey, smCharge, Finsupp.single_apply, ite_and, eq_comm]
  rfl

theorem exactSMResolvedCharacter_isPureSMChargeSpectrum
    {A : Type*} (generations : ℤ) (k : Charges A) :
    IsPureSMChargeSpectrum
      (exactSMResolvedCharacter generations k) generations k where
  quark := exactSMResolvedCharacter_quarkProfile generations k
  up := exactSMResolvedCharacter_upProfile generations k
  down := exactSMResolvedCharacter_downProfile generations k
  lepton := exactSMResolvedCharacter_leptonProfile generations k
  electron := exactSMResolvedCharacter_electronProfile generations k

theorem exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum
    {A : Type*} (generations : ℤ) (k : Charges A)
    (singlets : A →₀ ℤ) :
    IsPureSMChargeSpectrum
      (exactSMWithSingletsResolvedCharacter generations k singlets)
      generations k where
  quark := by
    calc
      quarkProfile
          (exactSMWithSingletsResolvedCharacter generations k singlets) =
          quarkProfile (exactSMResolvedCharacter generations k) +
            quarkProfile (singletResolvedCharacter singlets) := by
              ext q
              rfl
      _ = Finsupp.single k.quark generations + 0 := by
        rw [exactSMResolvedCharacter_quarkProfile]
        exact congrArg
          (Finsupp.single k.quark generations + ·)
          (by
            simpa [quarkProfile] using
              chargeProfile_singletResolvedCharacter_of_weight_ne_zero
                singlets reducedTenQ_ne_zero)
      _ = Finsupp.single k.quark generations := add_zero _
  up := by
    calc
      upProfile
          (exactSMWithSingletsResolvedCharacter generations k singlets) =
          upProfile (exactSMResolvedCharacter generations k) +
            upProfile (singletResolvedCharacter singlets) := by
              ext q
              rfl
      _ = Finsupp.single k.up generations + 0 := by
        rw [exactSMResolvedCharacter_upProfile]
        exact congrArg
          (Finsupp.single k.up generations + ·)
          (by
            simpa [upProfile] using
              chargeProfile_singletResolvedCharacter_of_weight_ne_zero
                singlets reducedTenUp_ne_zero)
      _ = Finsupp.single k.up generations := add_zero _
  down := by
    calc
      downProfile
          (exactSMWithSingletsResolvedCharacter generations k singlets) =
          downProfile (exactSMResolvedCharacter generations k) +
            downProfile (singletResolvedCharacter singlets) := by
              ext q
              rfl
      _ = Finsupp.single k.down generations + 0 := by
        rw [exactSMResolvedCharacter_downProfile]
        exact congrArg
          (Finsupp.single k.down generations + ·)
          (by
            simpa [downProfile] using
              chargeProfile_singletResolvedCharacter_of_weight_ne_zero
                singlets reducedBarFiveDown_ne_zero)
      _ = Finsupp.single k.down generations := add_zero _
  lepton := by
    calc
      leptonProfile
          (exactSMWithSingletsResolvedCharacter generations k singlets) =
          leptonProfile (exactSMResolvedCharacter generations k) +
            leptonProfile (singletResolvedCharacter singlets) := by
              ext q
              rfl
      _ = Finsupp.single k.lepton generations + 0 := by
        rw [exactSMResolvedCharacter_leptonProfile]
        exact congrArg
          (Finsupp.single k.lepton generations + ·)
          (by
            simpa [leptonProfile] using
              chargeProfile_singletResolvedCharacter_of_weight_ne_zero
                singlets reducedBarFiveLepton_ne_zero)
      _ = Finsupp.single k.lepton generations := add_zero _
  electron := by
    calc
      electronProfile
          (exactSMWithSingletsResolvedCharacter generations k singlets) =
          electronProfile (exactSMResolvedCharacter generations k) +
            electronProfile (singletResolvedCharacter singlets) := by
              ext q
              rfl
      _ = Finsupp.single k.electron generations + 0 := by
        rw [exactSMResolvedCharacter_electronProfile]
        exact congrArg
          (Finsupp.single k.electron generations + ·)
          (by
            simpa [electronProfile] using
              chargeProfile_singletResolvedCharacter_of_weight_ne_zero
                singlets reducedTenElectron_ne_zero)
      _ = Finsupp.single k.electron generations := add_zero _

end

end GUT.StandardSMCharacterTarget
