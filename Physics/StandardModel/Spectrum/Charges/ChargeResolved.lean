import Math.LieGroups.SpecialUnitary.RankFive.WeylOrbit
import Physics.StandardModel.Operators.Selection.AbelianProtonCharge
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.ZMod.Basic

open Math

/-!
# Rank-four weights with independent Abelian charge labels

The reduced weight removes the common diagonal exponent. Its charge label
is independent of this quotient. The optional chargeResolved map pushes
raw U(5) degrees into a chosen additive charge group, summing all collisions;
it is not an intrinsic determinant charge on SU(5).

This module contains the coefficient algebra only. An actual gauge
representation must supply its own checked character and support bridge.
Existing declaration namespaces are retained for compatibility.
-/

open scoped BigOperators

namespace Physics
namespace StandardAbelianCharge

open StandardSU5Orbit

noncomputable section

abbrev RawWeight := StandardSU5Orbit.Weight
abbrev RawCharacter := StandardSU5Orbit.Poly
abbrev ReducedWeight := Fin 4 -> ℤ

/-- Remove the common diagonal exponent by making the fifth coordinate zero. -/
def normalizeWeight (e : RawWeight) : ReducedWeight :=
  fun i => e i.castSucc - e (Fin.last 4)

/-- Restore the omitted zero fifth coordinate. -/
def rawReducedWeight (w : ReducedWeight) : RawWeight :=
  Fin.snoc w 0

@[simp]
theorem rawReducedWeight_castSucc (w : ReducedWeight) (i : Fin 4) :
    rawReducedWeight w i.castSucc = w i := by
  simp [rawReducedWeight]

@[simp]
theorem rawReducedWeight_last (w : ReducedWeight) :
    rawReducedWeight w (Fin.last 4) = 0 := by
  exact Fin.snoc_last
    (α := fun _ : Fin 5 => ℤ) (p := w) (x := 0)

@[simp]
theorem normalizeWeight_rawReducedWeight (w : ReducedWeight) :
    normalizeWeight (rawReducedWeight w) = w := by
  funext i
  rw [normalizeWeight, rawReducedWeight_castSucc,
    rawReducedWeight_last, sub_zero]

theorem rawReducedWeight_normalizeWeight (e : RawWeight) :
    rawReducedWeight (normalizeWeight e) =
      fun i => e i - e (Fin.last 4) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [normalizeWeight]
  · rw [rawReducedWeight_last, sub_self]

theorem normalizeWeight_sub_const (e : RawWeight) (c : ℤ) :
    normalizeWeight (fun i => e i - c) = normalizeWeight e := by
  funext i
  simp [normalizeWeight]

/-- Two raw weights have the same normal form exactly when they differ by
a common diagonal shift. This does not identify independent residual charges. -/
theorem normalizeWeight_eq_iff (e f : RawWeight) :
    normalizeWeight e = normalizeWeight f ↔
      ∃ c : ℤ, e = fun i => f i + c := by
  constructor
  · intro h
    refine ⟨e (Fin.last 4) - f (Fin.last 4), ?_⟩
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hj := congrFun h j
      simp only [normalizeWeight] at hj
      omega
    · omega
  · rintro ⟨c, rfl⟩
    funext i
    simp [normalizeWeight]

theorem normalizeWeight_surjective : Function.Surjective normalizeWeight :=
  fun w => ⟨rawReducedWeight w, normalizeWeight_rawReducedWeight w⟩

/-- The induced `S_5` action on the rank-four `SU(5)` weight normal form. -/
def permuteReducedWeight
    (sigma : Equiv.Perm (Fin 5)) (w : ReducedWeight) : ReducedWeight :=
  normalizeWeight
    (StandardSU5Orbit.permuteWeight sigma (rawReducedWeight w))

theorem permuteReducedWeight_normalizeWeight
    (sigma : Equiv.Perm (Fin 5)) (e : RawWeight) :
    permuteReducedWeight sigma (normalizeWeight e) =
      normalizeWeight (StandardSU5Orbit.permuteWeight sigma e) := by
  rw [permuteReducedWeight, rawReducedWeight_normalizeWeight]
  change
    normalizeWeight
        (fun i => e (sigma.symm i) - e (Fin.last 4)) =
      normalizeWeight (fun i => e (sigma.symm i))
  exact normalizeWeight_sub_const _ _

@[simp]
theorem permuteReducedWeight_one (w : ReducedWeight) :
    permuteReducedWeight 1 w = w := by
  change normalizeWeight (rawReducedWeight w) = w
  exact normalizeWeight_rawReducedWeight w

theorem permuteReducedWeight_mul
    (sigma tau : Equiv.Perm (Fin 5)) (w : ReducedWeight) :
    permuteReducedWeight sigma (permuteReducedWeight tau w) =
      permuteReducedWeight (sigma * tau) w := by
  change
    permuteReducedWeight sigma
        (normalizeWeight
          (StandardSU5Orbit.permuteWeight tau (rawReducedWeight w))) =
      normalizeWeight
        (StandardSU5Orbit.permuteWeight (sigma * tau)
          (rawReducedWeight w))
  rw [permuteReducedWeight_normalizeWeight]
  rfl

theorem permuteReducedWeight_injective (sigma : Equiv.Perm (Fin 5)) :
    Function.Injective (permuteReducedWeight sigma) := by
  intro w v h
  have hone : sigma.symm * sigma = 1 := by
    ext i
    simp
  have hcancel (x : ReducedWeight) :
      permuteReducedWeight sigma.symm (permuteReducedWeight sigma x) = x := by
    rw [permuteReducedWeight_mul, hone, permuteReducedWeight_one]
  calc
    w = permuteReducedWeight sigma.symm (permuteReducedWeight sigma w) :=
      (hcancel w).symm
    _ = permuteReducedWeight sigma.symm (permuteReducedWeight sigma v) :=
      congrArg (permuteReducedWeight sigma.symm) h
    _ = v := hcancel v

abbrev ResolvedKey (A : Type*) := ReducedWeight × A
abbrev ResolvedCharacter (A : Type*) := ResolvedKey A →₀ ℤ

/-- Weyl permutations act on the `SU(5)` weight and leave the residual charge
label fixed. -/
def permuteKey {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (x : ResolvedKey A) : ResolvedKey A :=
  (permuteReducedWeight sigma x.1, x.2)

theorem permuteKey_injective {A : Type*} (sigma : Equiv.Perm (Fin 5)) :
    Function.Injective (permuteKey (A := A) sigma) := by
  rintro ⟨w, q⟩ ⟨v, r⟩ h
  simp only [permuteKey, Prod.mk.injEq] at h
  exact Prod.ext (permuteReducedWeight_injective sigma h.1) h.2

def permuteResolved {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (p : ResolvedCharacter A) :
    ResolvedCharacter A :=
  Finsupp.mapDomain (permuteKey sigma) p

def ResolvedWeylInvariant {A : Type*} (p : ResolvedCharacter A) : Prop :=
  ∀ sigma : Equiv.Perm (Fin 5), permuteResolved sigma p = p

theorem resolved_coeff_permute_eq {A : Type*}
    (p : ResolvedCharacter A) (h : ResolvedWeylInvariant p)
    (sigma : Equiv.Perm (Fin 5)) (x : ResolvedKey A) :
    p (permuteKey sigma x) = p x := by
  have hp := congrArg
    (fun q : ResolvedCharacter A => q (permuteKey sigma x)) (h sigma)
  rw [permuteResolved,
    Finsupp.mapDomain_apply_of_injective (permuteKey_injective sigma)] at hp
  exact hp.symm

/-!
## Charge projection
-/

/-- Degree under the common central circle of `U(5)`. -/
def totalDegree (e : RawWeight) : ℤ :=
  ∑ i, e i

theorem totalDegree_permuteWeight
    (sigma : Equiv.Perm (Fin 5)) (e : RawWeight) :
    totalDegree (StandardSU5Orbit.permuteWeight sigma e) = totalDegree e := by
  exact Equiv.sum_comp sigma.symm e

def reducedTenQ : ReducedWeight :=
  normalizeWeight (StandardSU5Orbit.tenQ 0)

def reducedTenUp : ReducedWeight :=
  normalizeWeight (StandardSU5Orbit.tenUp 0)

def reducedTenElectron : ReducedWeight :=
  normalizeWeight (StandardSU5Orbit.tenElectron 0)

def reducedBarFiveDown : ReducedWeight :=
  normalizeWeight (StandardSU5Orbit.barFiveDown 0)

def reducedBarFiveLepton : ReducedWeight :=
  normalizeWeight (StandardSU5Orbit.barFiveLepton 0)

theorem normalizeWeight_tenQ (k : ℤ) :
    normalizeWeight (StandardSU5Orbit.tenQ k) = reducedTenQ := by
  funext i
  fin_cases i <;>
    simp [normalizeWeight, reducedTenQ, StandardSU5Orbit.tenQ,
      StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate]

theorem normalizeWeight_tenUp (k : ℤ) :
    normalizeWeight (StandardSU5Orbit.tenUp k) = reducedTenUp := by
  funext i
  fin_cases i <;>
    simp [normalizeWeight, reducedTenUp, StandardSU5Orbit.tenUp,
      StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate]

theorem normalizeWeight_tenElectron (k : ℤ) :
    normalizeWeight (StandardSU5Orbit.tenElectron k) =
      reducedTenElectron := by
  funext i
  fin_cases i <;>
    simp [normalizeWeight, reducedTenElectron,
      StandardSU5Orbit.tenElectron, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]

theorem normalizeWeight_barFiveDown (k : ℤ) :
    normalizeWeight (StandardSU5Orbit.barFiveDown k) =
      reducedBarFiveDown := by
  funext i
  fin_cases i <;>
    simp [normalizeWeight, reducedBarFiveDown,
      StandardSU5Orbit.barFiveDown, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]

theorem normalizeWeight_barFiveLepton (k : ℤ) :
    normalizeWeight (StandardSU5Orbit.barFiveLepton k) =
      reducedBarFiveLepton := by
  funext i
  fin_cases i <;>
    simp [normalizeWeight, reducedBarFiveLepton,
      StandardSU5Orbit.barFiveLepton, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]

theorem totalDegree_tenQ (k : ℤ) :
    totalDegree (StandardSU5Orbit.tenQ k) = 5 * k + 2 := by
  simp [totalDegree, StandardSU5Orbit.tenQ,
    StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate,
    Fin.sum_univ_five]
  ring

theorem totalDegree_tenUp (k : ℤ) :
    totalDegree (StandardSU5Orbit.tenUp k) = 5 * k + 2 := by
  simp [totalDegree, StandardSU5Orbit.tenUp,
    StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate,
    Fin.sum_univ_five]
  ring

theorem totalDegree_tenElectron (k : ℤ) :
    totalDegree (StandardSU5Orbit.tenElectron k) = 5 * k + 2 := by
  simp [totalDegree, StandardSU5Orbit.tenElectron,
    StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate,
    Fin.sum_univ_five]
  ring

theorem totalDegree_barFiveDown (k : ℤ) :
    totalDegree (StandardSU5Orbit.barFiveDown k) = 5 * k - 1 := by
  simp [totalDegree, StandardSU5Orbit.barFiveDown,
    StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate]

theorem totalDegree_barFiveLepton (k : ℤ) :
    totalDegree (StandardSU5Orbit.barFiveLepton k) = 5 * k - 1 := by
  simp [totalDegree, StandardSU5Orbit.barFiveLepton,
    StandardSU5Orbit.residualShift, StandardSU5Orbit.coordinate]

/-- Resolve a raw `U(5)` torus weight into an `SU(5)` weight and an Abelian
residual charge. -/
def projectKey {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (e : RawWeight) : ResolvedKey A :=
  (normalizeWeight e, charge (totalDegree e))

theorem projectKey_tenQ {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (k : ℤ) :
    projectKey charge (StandardSU5Orbit.tenQ k) =
      (reducedTenQ, charge (5 * k + 2)) := by
  rw [projectKey, normalizeWeight_tenQ, totalDegree_tenQ]

theorem projectKey_tenUp {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (k : ℤ) :
    projectKey charge (StandardSU5Orbit.tenUp k) =
      (reducedTenUp, charge (5 * k + 2)) := by
  rw [projectKey, normalizeWeight_tenUp, totalDegree_tenUp]

theorem projectKey_tenElectron {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (k : ℤ) :
    projectKey charge (StandardSU5Orbit.tenElectron k) =
      (reducedTenElectron, charge (5 * k + 2)) := by
  rw [projectKey, normalizeWeight_tenElectron, totalDegree_tenElectron]

theorem projectKey_barFiveDown {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (k : ℤ) :
    projectKey charge (StandardSU5Orbit.barFiveDown k) =
      (reducedBarFiveDown, charge (5 * k - 1)) := by
  rw [projectKey, normalizeWeight_barFiveDown,
    totalDegree_barFiveDown]

theorem projectKey_barFiveLepton {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (k : ℤ) :
    projectKey charge (StandardSU5Orbit.barFiveLepton k) =
      (reducedBarFiveLepton, charge (5 * k - 1)) := by
  rw [projectKey, normalizeWeight_barFiveLepton,
    totalDegree_barFiveLepton]

/-- Reduction of the integer central degree to a cyclic residual charge. -/
def cyclicCharge (N : ℕ) : ℤ →+ ZMod N :=
  Int.castAddHom (ZMod N)

@[simp]
theorem cyclicCharge_apply (N : ℕ) (k : ℤ) :
    cyclicCharge N k = (k : ZMod N) :=
  rfl

theorem projectKey_tenQ_cyclic (N : ℕ) (k : ℤ) :
    projectKey (cyclicCharge N) (StandardSU5Orbit.tenQ k) =
      (reducedTenQ, ((5 * k + 2 : ℤ) : ZMod N)) := by
  rw [projectKey_tenQ]
  rfl

theorem projectKey_barFiveDown_cyclic (N : ℕ) (k : ℤ) :
    projectKey (cyclicCharge N) (StandardSU5Orbit.barFiveDown k) =
      (reducedBarFiveDown, ((5 * k - 1 : ℤ) : ZMod N)) := by
  rw [projectKey_barFiveDown]
  rfl

theorem projectKey_permuteWeight {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (sigma : Equiv.Perm (Fin 5)) (e : RawWeight) :
    projectKey charge (StandardSU5Orbit.permuteWeight sigma e) =
      permuteKey sigma (projectKey charge e) := by
  apply Prod.ext
  · exact (permuteReducedWeight_normalizeWeight sigma e).symm
  · change
      charge (totalDegree (StandardSU5Orbit.permuteWeight sigma e)) =
        charge (totalDegree e)
    rw [totalDegree_permuteWeight]

/-- Push a finite `U(5)` character to charge-resolved `SU(5)` weights.  The
non-injective `mapDomain` deliberately sums all integer lifts of one finite
residual charge. -/
def chargeResolved {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (p : RawCharacter) : ResolvedCharacter A :=
  Finsupp.mapDomain (projectKey charge) p

theorem chargeResolved_isWeylInvariant
    {A : Type*} [AddCommGroup A]
    (charge : ℤ →+ A) (p : RawCharacter)
    (hp : StandardSU5Orbit.WeylInvariant p) :
    ResolvedWeylInvariant (chargeResolved charge p) := by
  intro sigma
  unfold permuteResolved chargeResolved
  calc
    Finsupp.mapDomain (permuteKey sigma)
          (Finsupp.mapDomain (projectKey charge) p) =
        Finsupp.mapDomain
          (permuteKey sigma ∘ projectKey charge) p :=
      Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          (projectKey charge ∘ StandardSU5Orbit.permuteWeight sigma) p := by
      apply Finsupp.mapDomain_congr
      intro e _he
      exact (projectKey_permuteWeight charge sigma e).symm
    _ = Finsupp.mapDomain (projectKey charge)
          (Finsupp.mapDomain
            (StandardSU5Orbit.permuteWeight sigma) p) :=
      Finsupp.mapDomain_comp
    _ = Finsupp.mapDomain (projectKey charge) p := by
      rw [show Finsupp.mapDomain
          (StandardSU5Orbit.permuteWeight sigma) p = p from hp sigma]

/-!
## Standard Model orbit profiles
-/

theorem permuteReducedWeight_swap31_tenQ :
    permuteReducedWeight (Equiv.swap (3 : Fin 5) 1) reducedTenQ =
      reducedTenUp := by
  rw [reducedTenQ, reducedTenUp, permuteReducedWeight_normalizeWeight,
    StandardSU5Orbit.permuteWeight_swap31_tenQ]

theorem permuteReducedWeight_swap04_tenQ :
    permuteReducedWeight (Equiv.swap (0 : Fin 5) 4) reducedTenQ =
      reducedTenElectron := by
  rw [reducedTenQ, reducedTenElectron,
    permuteReducedWeight_normalizeWeight,
    StandardSU5Orbit.permuteWeight_swap04_tenQ]

theorem permuteReducedWeight_swap03_barFiveDown :
    permuteReducedWeight (Equiv.swap (0 : Fin 5) 3) reducedBarFiveDown =
      reducedBarFiveLepton := by
  rw [reducedBarFiveDown, reducedBarFiveLepton,
    permuteReducedWeight_normalizeWeight,
    StandardSU5Orbit.permuteWeight_swap03_barFiveDown]

theorem ten_resolved_coefficients_equal {A : Type*}
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p) (q : A) :
    p (reducedTenQ, q) = p (reducedTenUp, q) ∧
      p (reducedTenQ, q) = p (reducedTenElectron, q) := by
  constructor
  · have h := resolved_coeff_permute_eq p hp
      (Equiv.swap (3 : Fin 5) 1) (reducedTenQ, q)
    simpa [permuteKey, permuteReducedWeight_swap31_tenQ] using h.symm
  · have h := resolved_coeff_permute_eq p hp
      (Equiv.swap (0 : Fin 5) 4) (reducedTenQ, q)
    simpa [permuteKey, permuteReducedWeight_swap04_tenQ] using h.symm

theorem barFive_resolved_coefficients_equal {A : Type*}
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p) (q : A) :
    p (reducedBarFiveDown, q) = p (reducedBarFiveLepton, q) := by
  have h := resolved_coeff_permute_eq p hp
    (Equiv.swap (0 : Fin 5) 3) (reducedBarFiveDown, q)
  simpa [permuteKey, permuteReducedWeight_swap03_barFiveDown] using h.symm

/-- The finite charge profile at one normalized `SU(5)` weight. -/
def chargeProfile {A : Type*}
    (p : ResolvedCharacter A) (w : ReducedWeight) : A →₀ ℤ :=
  Finsupp.comapDomain (fun q => (w, q)) p (by
    intro q _ r _ h
    exact congrArg Prod.snd h)

@[simp]
theorem chargeProfile_apply {A : Type*}
    (p : ResolvedCharacter A) (w : ReducedWeight) (q : A) :
    chargeProfile p w q = p (w, q) := by
  rfl

def quarkProfile {A : Type*} (p : ResolvedCharacter A) : A →₀ ℤ :=
  chargeProfile p reducedTenQ

def upProfile {A : Type*} (p : ResolvedCharacter A) : A →₀ ℤ :=
  chargeProfile p reducedTenUp

def electronProfile {A : Type*} (p : ResolvedCharacter A) : A →₀ ℤ :=
  chargeProfile p reducedTenElectron

def downProfile {A : Type*} (p : ResolvedCharacter A) : A →₀ ℤ :=
  chargeProfile p reducedBarFiveDown

def leptonProfile {A : Type*} (p : ResolvedCharacter A) : A →₀ ℤ :=
  chargeProfile p reducedBarFiveLepton

theorem sm_charge_profiles_equal {A : Type*}
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p) :
    quarkProfile p = upProfile p ∧
      quarkProfile p = electronProfile p ∧
      downProfile p = leptonProfile p := by
  constructor
  · ext q
    exact (ten_resolved_coefficients_equal p hp q).1
  constructor
  · ext q
    exact (ten_resolved_coefficients_equal p hp q).2
  · ext q
    exact barFive_resolved_coefficients_equal p hp q

/-- A charge assignment selected from one occupied `10` sector and one
occupied anti-fundamental sector. -/
def sectorCharges {A : Type*} (q r : A) :
    StandardBranchProtonObstruction.Charges A where
  quark := q
  up := q
  down := r
  lepton := r
  electron := q

@[simp]
theorem sectorCharges_su5OrbitCompatible
    {A : Type*} (q r : A) :
    StandardBranchProtonObstruction.SU5OrbitCompatible
      (sectorCharges q r) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Every field type required by the two standard gauge-mediated contractions
occurs in the selected charge sectors. -/
def ChargesSupported {A : Type*}
    (p : ResolvedCharacter A)
    (k : StandardBranchProtonObstruction.Charges A) : Prop :=
  quarkProfile p k.quark ≠ 0 ∧
    upProfile p k.up ≠ 0 ∧
    downProfile p k.down ≠ 0 ∧
    leptonProfile p k.lepton ≠ 0 ∧
    electronProfile p k.electron ≠ 0

theorem exists_apply_ne_zero_of_ne_zero {A : Type*}
    (f : A →₀ ℤ) (hf : f ≠ 0) :
    ∃ q, f q ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  ext q
  exact h q

/-- The family-dependent form of the standard charge-orbit bridge conclusion: nonempty `10` and
anti-fundamental profiles contain a common-charge representative of every SM
field needed by the two proton-decay contractions. -/
theorem exists_supported_su5OrbitCompatible
    {A : Type*}
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (hTen : quarkProfile p ≠ 0)
    (hBarFive : downProfile p ≠ 0) :
    ∃ k : StandardBranchProtonObstruction.Charges A,
      ChargesSupported p k ∧
        StandardBranchProtonObstruction.SU5OrbitCompatible k := by
  obtain ⟨q, hq⟩ := exists_apply_ne_zero_of_ne_zero (quarkProfile p) hTen
  obtain ⟨r, hr⟩ := exists_apply_ne_zero_of_ne_zero
    (downProfile p) hBarFive
  rcases sm_charge_profiles_equal p hp with ⟨hQU, hQE, hDL⟩
  refine ⟨sectorCharges q r, ?_, sectorCharges_su5OrbitCompatible q r⟩
  refine ⟨hq, ?_, hr, ?_, ?_⟩
  · change upProfile p q ≠ 0
    rw [← hQU]
    exact hq
  · change leptonProfile p r ≠ 0
    rw [← hDL]
    exact hr
  · change electronProfile p q ≠ 0
    rw [← hQE]
    exact hq

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality for arbitrary family-dependent charge profiles.  It
exhibits occupied charge sectors for which both proton functionals are
neutral. -/
theorem exists_supported_neutral_proton_sectors
    {A : Type*} [AddCommGroup A]
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (hTen : quarkProfile p ≠ 0)
    (hBarFive : downProfile p ≠ 0) :
    ∃ k : StandardBranchProtonObstruction.Charges A,
      ChargesSupported p k ∧
        StandardBranchProtonObstruction.protonFirst k = 0 ∧
        StandardBranchProtonObstruction.protonSecond k = 0 := by
  obtain ⟨k, hkSupport, hkOrbit⟩ :=
    exists_supported_su5OrbitCompatible p hp hTen hBarFive
  exact ⟨k, hkSupport,
    StandardBranchProtonObstruction.proton_functionals_eq_zero_of_su5OrbitCompatible
      k hkOrbit⟩

/-!
## Exact SM-only interpretation and the standard charge-orbit bridge to Abelian proton-operator neutrality composition
-/

open StandardBranchProtonObstruction

/-- A charge-resolved character has exactly one nonzero chiral charge sector
of multiplicity `generations` for each of the five SM multiplet types. -/
structure IsPureSMChargeSpectrum {A : Type*}
    (p : ResolvedCharacter A) (generations : ℤ) (k : Charges A) : Prop where
  quark : quarkProfile p = Finsupp.single k.quark generations
  up : upProfile p = Finsupp.single k.up generations
  down : downProfile p = Finsupp.single k.down generations
  lepton : leptonProfile p = Finsupp.single k.lepton generations
  electron : electronProfile p = Finsupp.single k.electron generations

theorem su5OrbitCompatible_of_pureSM
    {A : Type*} [AddCommGroup A]
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A) (hSM : IsPureSMChargeSpectrum p generations k) :
    SU5OrbitCompatible k := by
  rcases sm_charge_profiles_equal p hp with ⟨hQU, hQE, hDL⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.single_left_injective hgenerations (calc
      Finsupp.single k.quark generations = quarkProfile p := hSM.quark.symm
      _ = upProfile p := hQU
      _ = Finsupp.single k.up generations := hSM.up)
  · exact Finsupp.single_left_injective hgenerations (calc
      Finsupp.single k.quark generations = quarkProfile p := hSM.quark.symm
      _ = electronProfile p := hQE
      _ = Finsupp.single k.electron generations := hSM.electron)
  · exact Finsupp.single_left_injective hgenerations (calc
      Finsupp.single k.down generations = downProfile p := hSM.down.symm
      _ = leptonProfile p := hDL
      _ = Finsupp.single k.lepton generations := hSM.lepton)

/-- Main algebraic standard-branch path: standard charge-orbit bridge charge-profile equality followed
by the Abelian proton-operator neutrality Abelian charge-group calculation.  No anomaly equation is used. -/
theorem proton_functionals_eq_zero_of_pureSM
    {A : Type*} [AddCommGroup A]
    (p : ResolvedCharacter A) (hp : ResolvedWeylInvariant p)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A) (hSM : IsPureSMChargeSpectrum p generations k) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  proton_functionals_eq_zero_of_su5OrbitCompatible k
    (su5OrbitCompatible_of_pureSM p hp generations hgenerations k hSM)


end
end StandardAbelianCharge
end Physics
