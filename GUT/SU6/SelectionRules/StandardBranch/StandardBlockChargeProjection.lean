import GUT.SU6.SelectionRules.StandardBranch.StandardBlockGaugeCancellation
import Mathlib.Tactic

open Physics

open Math

/-!
# Charge resolution for an arbitrary standard block-gauge lift

For a general element of the standard `3+2+1` compact centralizer, the five
independent ambient torus coordinates carry color/weak block charges
`(c,c,c,w,w)`.  Unlike the standard-central circle, this action need not be a
homomorphic function of total degree: the conventional `Y5/X` cocharacter
lattice has index five.  We therefore retain the unnormalized rank-five
weight until after its block charge has been evaluated.

The definitions below use `Finsupp.mapDomain`, so collisions of characters of
a finite Abelian residual group are summed.  The main goal of this file is to
transport the raw `SU(5)` Weyl symmetry to corrected physical charge profiles
without assuming roots of residual-group characters.
-/

namespace GUT
namespace StandardBlockChargeProjection

open scoped BigOperators

open FiniteAbelianChargeSectors
open StandardAbelianCharge
open StandardBlockGaugeCancellation
open StandardBranchProtonObstruction
open StandardPhysicalSpectrumBridge
open WeakDoubletEmbeddingClassification
open ActualBlockCentralizer
open ActualCompactCentralizer
open CompactEmbeddingClassification

noncomputable section

universe u

abbrev RawWeight := StandardAbelianCharge.RawWeight
abbrev ReducedWeight := StandardAbelianCharge.ReducedWeight
abbrev ResolvedCharacter := StandardAbelianCharge.ResolvedCharacter

/-!
## Raw charge-resolved characters
-/

abbrev RawResolvedKey (A : Type*) := RawWeight × A
abbrev RawResolvedCharacter (A : Type*) := RawResolvedKey A →₀ ℤ

def permuteRawKey {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (x : RawResolvedKey A) :
    RawResolvedKey A :=
  (StandardSU5Orbit.permuteWeight sigma x.1, x.2)

theorem permuteRawKey_injective {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) :
    Function.Injective (permuteRawKey (A := A) sigma) := by
  rintro ⟨e, q⟩ ⟨f, r⟩ h
  apply Prod.ext
  · exact StandardSU5Orbit.permuteWeight_injective sigma
      (congrArg Prod.fst h)
  · simpa [permuteRawKey] using congrArg Prod.snd h

/-- The raw-key permutation as an actual equivalence. -/
def rawKeyPermEquiv {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) : RawResolvedKey A ≃ RawResolvedKey A where
  toFun := permuteRawKey sigma
  invFun := permuteRawKey sigma.symm
  left_inv x := by
    rcases x with ⟨e, q⟩
    apply Prod.ext
    · funext i
      simp [permuteRawKey, StandardSU5Orbit.permuteWeight]
    · rfl
  right_inv x := by
    rcases x with ⟨e, q⟩
    apply Prod.ext
    · funext i
      simp [permuteRawKey, StandardSU5Orbit.permuteWeight]
    · rfl

@[simp]
theorem rawKeyPermEquiv_apply {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (x : RawResolvedKey A) :
    rawKeyPermEquiv sigma x = permuteRawKey sigma x :=
  rfl

@[simp]
theorem rawKeyPermEquiv_symm_apply {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (x : RawResolvedKey A) :
    (rawKeyPermEquiv sigma).symm x = permuteRawKey sigma.symm x :=
  rfl

def permuteRawResolved {A : Type*}
    (sigma : Equiv.Perm (Fin 5)) (p : RawResolvedCharacter A) :
    RawResolvedCharacter A :=
  Finsupp.mapDomain (rawKeyPermEquiv sigma) p

def RawResolvedWeylInvariant {A : Type*}
    (p : RawResolvedCharacter A) : Prop :=
  ∀ sigma : Equiv.Perm (Fin 5), permuteRawResolved sigma p = p

/-!
## Block charge and physical projection
-/

def colorDegree (e : RawWeight) : ℤ :=
  e 0 + e 1 + e 2

def weakDegree (e : RawWeight) : ℤ :=
  e 3 + e 4

/-- Additive charge obtained by evaluating a raw ambient monomial on the
color and weak block characters. -/
def blockCharge {A : Type*} [AddCommGroup A]
    (color weak : A) (e : RawWeight) : A :=
  colorDegree e • color + weakDegree e • weak

def blockProjectKey {A : Type*} [AddCommGroup A]
    (color weak : A) (x : RawResolvedKey A) :
    StandardAbelianCharge.ResolvedKey A :=
  (normalizeWeight x.1, x.2 + blockCharge color weak x.1)

/-- Evaluate the block part before forgetting the raw lift.  Non-injective
projection deliberately sums finite-charge collisions. -/
def blockResolved {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A) : ResolvedCharacter A :=
  Finsupp.mapDomain (blockProjectKey color weak) p

/-- Restrict a raw resolved character to one normalized weight and retain
only its resulting physical charge profile. -/
def projectedProfile {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (target : ReducedWeight) : A →₀ ℤ :=
  Finsupp.mapDomain
    (fun x : RawResolvedKey A => x.2 + blockCharge color weak x.1)
    (p.filter fun x => normalizeWeight x.1 = target)

/-- Remove a fixed field-dependent block charge from a projected profile. -/
def correctedProjectedProfile {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (target : ReducedWeight) (base : A) : A →₀ ℤ :=
  Finsupp.mapDomain
    (fun x : RawResolvedKey A =>
      x.2 + blockCharge color weak x.1 - base)
    (p.filter fun x => normalizeWeight x.1 = target)

theorem chargeProfile_blockResolved
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (target : ReducedWeight) :
    chargeProfile (blockResolved color weak p) target =
      projectedProfile color weak p target := by
  classical
  ext q
  simp only [chargeProfile_apply, blockResolved, projectedProfile]
  simp [Finsupp.mapDomain, blockProjectKey, Finsupp.single_apply]
  rw [Finsupp.sum, Finsupp.sum]
  simp only [Finsupp.support_filter, Finset.sum_filter,
    Finsupp.filter_apply]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases htarget : normalizeWeight x.1 = target <;> simp [htarget]

theorem normalize_permuteWeight_eq_iff
    (sigma : Equiv.Perm (Fin 5))
    (source target : ReducedWeight)
    (hTarget : permuteReducedWeight sigma source = target)
    (e : RawWeight) :
    normalizeWeight (StandardSU5Orbit.permuteWeight sigma e) = target ↔
      normalizeWeight e = source := by
  rw [← permuteReducedWeight_normalizeWeight, ← hTarget]
  exact (permuteReducedWeight_injective sigma).eq_iff

theorem filter_permuteRawResolved
    {A : Type*} (sigma : Equiv.Perm (Fin 5))
    (p : RawResolvedCharacter A) (source target : ReducedWeight)
    (hTarget : permuteReducedWeight sigma source = target) :
    (permuteRawResolved sigma p).filter
        (fun x => normalizeWeight x.1 = target) =
      Finsupp.mapDomain (rawKeyPermEquiv sigma)
        (p.filter fun x => normalizeWeight x.1 = source) := by
  classical
  ext y
  simp only [Finsupp.filter_apply, permuteRawResolved,
    Finsupp.mapDomain_equiv_apply]
  let x := (rawKeyPermEquiv sigma).symm y
  have hy : rawKeyPermEquiv sigma x = y :=
    (rawKeyPermEquiv sigma).apply_symm_apply y
  have hPred := normalize_permuteWeight_eq_iff
    sigma source target hTarget x.1
  have hPred' : normalizeWeight y.1 = target ↔
      normalizeWeight x.1 = source := by
    rw [← hy]
    exact hPred
  by_cases hyt : normalizeWeight y.1 = target
  · have hxs := hPred'.mp hyt
    change normalizeWeight (permuteRawKey sigma.symm y).1 = source at hxs
    simp [hyt, hxs]
  · have hxs : normalizeWeight x.1 ≠ source :=
      fun hx => hyt (hPred'.mpr hx)
    change normalizeWeight (permuteRawKey sigma.symm y).1 ≠ source at hxs
    simp [hyt, hxs]

/-- Generic transport of a corrected physical profile across one raw Weyl
permutation. -/
theorem correctedProjectedProfile_eq_of_permute
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p)
    (sigma : Equiv.Perm (Fin 5))
    (source target : ReducedWeight) (sourceBase targetBase : A)
    (hTarget : permuteReducedWeight sigma source = target)
    (hLabel : ∀ x : RawResolvedKey A,
      normalizeWeight x.1 = source →
      (rawKeyPermEquiv sigma x).2 +
          blockCharge color weak (rawKeyPermEquiv sigma x).1 - targetBase =
        x.2 + blockCharge color weak x.1 - sourceBase) :
    correctedProjectedProfile color weak p target targetBase =
      correctedProjectedProfile color weak p source sourceBase := by
  classical
  calc
    correctedProjectedProfile color weak p target targetBase =
        correctedProjectedProfile color weak
          (permuteRawResolved sigma p) target targetBase := by
      rw [hp sigma]
    _ = Finsupp.mapDomain
          (fun x : RawResolvedKey A =>
            x.2 + blockCharge color weak x.1 - targetBase)
          (Finsupp.mapDomain (rawKeyPermEquiv sigma)
            (p.filter fun x => normalizeWeight x.1 = source)) := by
      rw [correctedProjectedProfile,
        filter_permuteRawResolved sigma p source target hTarget]
    _ = Finsupp.mapDomain
          ((fun x : RawResolvedKey A =>
              x.2 + blockCharge color weak x.1 - targetBase) ∘
            rawKeyPermEquiv sigma)
          (p.filter fun x => normalizeWeight x.1 = source) :=
      Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          (fun x : RawResolvedKey A =>
            x.2 + blockCharge color weak x.1 - sourceBase)
          (p.filter fun x => normalizeWeight x.1 = source) := by
      apply Finsupp.mapDomain_congr
      intro x hx
      apply hLabel x
      simpa using (Finset.mem_filter.mp
        (show x ∈ (p.filter
          fun y => normalizeWeight y.1 = source).support from hx)).2
    _ = correctedProjectedProfile color weak p source sourceBase := rfl

/-!
## Standard Model orbit calculations
-/

def determinantBlockCharge {A : Type*} [AddCommGroup A]
    (color weak : A) : A :=
  3 • color + 2 • weak

theorem rawWeight_reconstruct (e : RawWeight) :
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
      rawReducedWeight (normalizeWeight e) := by
  rw [rawReducedWeight_normalizeWeight]
  funext i
  simp [StandardSU5Orbit.residualShift]

theorem rawReducedWeight_reducedTenQ :
    rawReducedWeight reducedTenQ = StandardSU5Orbit.tenQ 0 := by
  decide

theorem rawReducedWeight_reducedTenUp :
    rawReducedWeight reducedTenUp = StandardSU5Orbit.tenUp 0 := by
  decide

theorem rawReducedWeight_reducedTenElectron :
    rawReducedWeight reducedTenElectron =
      StandardSU5Orbit.tenElectron (-1) := by
  decide

theorem rawReducedWeight_reducedBarFiveDown :
    rawReducedWeight reducedBarFiveDown =
      StandardSU5Orbit.barFiveDown 0 := by
  decide

theorem rawReducedWeight_reducedBarFiveLepton :
    rawReducedWeight reducedBarFiveLepton =
      StandardSU5Orbit.barFiveLepton 0 := by
  decide

theorem residualShift_add_rawReducedWeight_reducedTenQ (k : ℤ) :
    StandardSU5Orbit.residualShift k + rawReducedWeight reducedTenQ =
      StandardSU5Orbit.tenQ k := by
  rw [rawReducedWeight_reducedTenQ]
  ext i
  fin_cases i <;>
    simp [StandardSU5Orbit.tenQ, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]

theorem residualShift_add_rawReducedWeight_reducedTenUp (k : ℤ) :
    StandardSU5Orbit.residualShift k + rawReducedWeight reducedTenUp =
      StandardSU5Orbit.tenUp k := by
  rw [rawReducedWeight_reducedTenUp]
  ext i
  fin_cases i <;>
    simp [StandardSU5Orbit.tenUp, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]

theorem residualShift_add_rawReducedWeight_reducedTenElectron (k : ℤ) :
    StandardSU5Orbit.residualShift k +
        rawReducedWeight reducedTenElectron =
      StandardSU5Orbit.tenElectron (k - 1) := by
  rw [rawReducedWeight_reducedTenElectron]
  ext i
  fin_cases i <;>
    simp [StandardSU5Orbit.tenElectron, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]
  all_goals omega

theorem residualShift_add_rawReducedWeight_reducedBarFiveDown (k : ℤ) :
    StandardSU5Orbit.residualShift k +
        rawReducedWeight reducedBarFiveDown =
      StandardSU5Orbit.barFiveDown k := by
  rw [rawReducedWeight_reducedBarFiveDown]
  ext i
  fin_cases i <;>
    simp [StandardSU5Orbit.barFiveDown, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]
  all_goals omega

theorem residualShift_add_rawReducedWeight_reducedBarFiveLepton (k : ℤ) :
    StandardSU5Orbit.residualShift k +
        rawReducedWeight reducedBarFiveLepton =
      StandardSU5Orbit.barFiveLepton k := by
  rw [rawReducedWeight_reducedBarFiveLepton]
  ext i
  fin_cases i <;>
    simp [StandardSU5Orbit.barFiveLepton, StandardSU5Orbit.residualShift,
      StandardSU5Orbit.coordinate]
  all_goals omega

theorem eq_tenQ_of_normalizeWeight_eq
    (e : RawWeight) (h : normalizeWeight e = reducedTenQ) :
    e = StandardSU5Orbit.tenQ (e (Fin.last 4)) := by
  calc
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight (normalizeWeight e) := rawWeight_reconstruct e
    _ = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight reducedTenQ := by rw [h]
    _ = StandardSU5Orbit.tenQ (e (Fin.last 4)) :=
      residualShift_add_rawReducedWeight_reducedTenQ _

theorem eq_tenUp_of_normalizeWeight_eq
    (e : RawWeight) (h : normalizeWeight e = reducedTenUp) :
    e = StandardSU5Orbit.tenUp (e (Fin.last 4)) := by
  calc
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight (normalizeWeight e) := rawWeight_reconstruct e
    _ = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight reducedTenUp := by rw [h]
    _ = StandardSU5Orbit.tenUp (e (Fin.last 4)) :=
      residualShift_add_rawReducedWeight_reducedTenUp _

theorem eq_tenElectron_of_normalizeWeight_eq
    (e : RawWeight) (h : normalizeWeight e = reducedTenElectron) :
    e = StandardSU5Orbit.tenElectron (e (Fin.last 4) - 1) := by
  calc
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight (normalizeWeight e) := rawWeight_reconstruct e
    _ = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight reducedTenElectron := by rw [h]
    _ = StandardSU5Orbit.tenElectron (e (Fin.last 4) - 1) :=
      residualShift_add_rawReducedWeight_reducedTenElectron _

theorem eq_barFiveDown_of_normalizeWeight_eq
    (e : RawWeight) (h : normalizeWeight e = reducedBarFiveDown) :
    e = StandardSU5Orbit.barFiveDown (e (Fin.last 4)) := by
  calc
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight (normalizeWeight e) := rawWeight_reconstruct e
    _ = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight reducedBarFiveDown := by rw [h]
    _ = StandardSU5Orbit.barFiveDown (e (Fin.last 4)) :=
      residualShift_add_rawReducedWeight_reducedBarFiveDown _

theorem eq_barFiveLepton_of_normalizeWeight_eq
    (e : RawWeight) (h : normalizeWeight e = reducedBarFiveLepton) :
    e = StandardSU5Orbit.barFiveLepton (e (Fin.last 4)) := by
  calc
    e = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight (normalizeWeight e) := rawWeight_reconstruct e
    _ = StandardSU5Orbit.residualShift (e (Fin.last 4)) +
        rawReducedWeight reducedBarFiveLepton := by rw [h]
    _ = StandardSU5Orbit.barFiveLepton (e (Fin.last 4)) :=
      residualShift_add_rawReducedWeight_reducedBarFiveLepton _

theorem blockCharge_tenQ {A : Type*} [AddCommGroup A]
    (color weak : A) (k : ℤ) :
    blockCharge color weak (StandardSU5Orbit.tenQ k) =
      k • determinantBlockCharge color weak + color + weak := by
  simp [blockCharge, colorDegree, weakDegree, determinantBlockCharge,
    StandardSU5Orbit.tenQ, StandardSU5Orbit.residualShift,
    StandardSU5Orbit.coordinate]
  module

theorem blockCharge_tenUp {A : Type*} [AddCommGroup A]
    (color weak : A) (k : ℤ) :
    blockCharge color weak (StandardSU5Orbit.tenUp k) =
      k • determinantBlockCharge color weak + color + color := by
  simp [blockCharge, colorDegree, weakDegree, determinantBlockCharge,
    StandardSU5Orbit.tenUp, StandardSU5Orbit.residualShift,
    StandardSU5Orbit.coordinate]
  module

theorem blockCharge_tenElectron {A : Type*} [AddCommGroup A]
    (color weak : A) (k : ℤ) :
    blockCharge color weak (StandardSU5Orbit.tenElectron k) =
      k • determinantBlockCharge color weak + weak + weak := by
  simp [blockCharge, colorDegree, weakDegree, determinantBlockCharge,
    StandardSU5Orbit.tenElectron, StandardSU5Orbit.residualShift,
    StandardSU5Orbit.coordinate]
  module

theorem blockCharge_barFiveDown {A : Type*} [AddCommGroup A]
    (color weak : A) (k : ℤ) :
    blockCharge color weak (StandardSU5Orbit.barFiveDown k) =
      k • determinantBlockCharge color weak - color := by
  simp [blockCharge, colorDegree, weakDegree, determinantBlockCharge,
    StandardSU5Orbit.barFiveDown, StandardSU5Orbit.residualShift,
    StandardSU5Orbit.coordinate]
  module

theorem blockCharge_barFiveLepton {A : Type*} [AddCommGroup A]
    (color weak : A) (k : ℤ) :
    blockCharge color weak (StandardSU5Orbit.barFiveLepton k) =
      k • determinantBlockCharge color weak - weak := by
  simp [blockCharge, colorDegree, weakDegree, determinantBlockCharge,
    StandardSU5Orbit.barFiveLepton, StandardSU5Orbit.residualShift,
    StandardSU5Orbit.coordinate]
  module

/-- Translation of a finite charge profile.  `mapDomain` sums collisions, so
this remains correct in finite charge groups. -/
def shiftProfile {A : Type*} [AddCommGroup A]
    (shift : A) (p : A →₀ ℤ) : A →₀ ℤ :=
  Finsupp.mapDomain (fun q => q + shift) p

@[simp]
theorem shiftProfile_apply
    {A : Type*} [AddCommGroup A]
    (shift : A) (p : A →₀ ℤ) (q : A) :
    shiftProfile shift p q = p (q - shift) := by
  let translate : A → A := fun a => a + shift
  have hTranslate : Function.Injective translate := by
    intro a b h
    exact add_right_cancel h
  calc
    shiftProfile shift p q =
        shiftProfile shift p ((q - shift) + shift) := by
      rw [sub_add_cancel]
    _ = p (q - shift) := by
      exact Finsupp.mapDomain_apply_of_injective hTranslate p (q - shift)

theorem shiftProfile_ne_zero_iff
    {A : Type*} [AddCommGroup A]
    (shift : A) (p : A →₀ ℤ) :
    shiftProfile shift p ≠ 0 ↔ p ≠ 0 := by
  let translate : A → A := fun q => q + shift
  have hTranslate : Function.Injective translate := by
    intro a b h
    exact add_right_cancel h
  constructor
  · intro hShift hp
    apply hShift
    rw [hp]
    simp [shiftProfile]
  · intro hp hShift
    apply hp
    apply Finsupp.mapDomain_injective (M := ℤ) hTranslate
    simpa [shiftProfile, translate] using hShift

theorem correctedProjectedProfile_eq_shiftProfile
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (target : ReducedWeight) (base : A) :
    correctedProjectedProfile color weak p target base =
      shiftProfile (-base)
        (chargeProfile (blockResolved color weak p) target) := by
  rw [chargeProfile_blockResolved]
  unfold correctedProjectedProfile projectedProfile shiftProfile
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro x _hx
  simp only [Function.comp_apply]
  abel

theorem correctedTenQ_eq_tenUp
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p) :
    correctedProjectedProfile color weak p reducedTenQ (color + weak) =
      correctedProjectedProfile color weak p reducedTenUp (color + color) := by
  symm
  apply correctedProjectedProfile_eq_of_permute color weak p hp
    (Equiv.swap (3 : Fin 5) 1) reducedTenQ reducedTenUp
    (color + weak) (color + color)
    permuteReducedWeight_swap31_tenQ
  rintro ⟨e, q⟩ he
  rw [eq_tenQ_of_normalizeWeight_eq e he]
  change
    q + blockCharge color weak
          (StandardSU5Orbit.permuteWeight (Equiv.swap (3 : Fin 5) 1)
            (StandardSU5Orbit.tenQ (e (Fin.last 4)))) -
        (color + color) =
      q + blockCharge color weak
          (StandardSU5Orbit.tenQ (e (Fin.last 4))) - (color + weak)
  rw [StandardSU5Orbit.permuteWeight_swap31_tenQ,
    blockCharge_tenUp, blockCharge_tenQ]
  abel

theorem correctedTenQ_eq_tenElectron
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p) :
    correctedProjectedProfile color weak p reducedTenQ (color + weak) =
      correctedProjectedProfile color weak p reducedTenElectron (weak + weak) := by
  symm
  apply correctedProjectedProfile_eq_of_permute color weak p hp
    (Equiv.swap (0 : Fin 5) 4) reducedTenQ reducedTenElectron
    (color + weak) (weak + weak)
    permuteReducedWeight_swap04_tenQ
  rintro ⟨e, q⟩ he
  rw [eq_tenQ_of_normalizeWeight_eq e he]
  change
    q + blockCharge color weak
          (StandardSU5Orbit.permuteWeight (Equiv.swap (0 : Fin 5) 4)
            (StandardSU5Orbit.tenQ (e (Fin.last 4)))) -
        (weak + weak) =
      q + blockCharge color weak
          (StandardSU5Orbit.tenQ (e (Fin.last 4))) - (color + weak)
  rw [StandardSU5Orbit.permuteWeight_swap04_tenQ,
    blockCharge_tenElectron, blockCharge_tenQ]
  abel

theorem correctedBarFiveDown_eq_barFiveLepton
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p) :
    correctedProjectedProfile color weak p reducedBarFiveDown (-color) =
      correctedProjectedProfile color weak p reducedBarFiveLepton (-weak) := by
  symm
  apply correctedProjectedProfile_eq_of_permute color weak p hp
    (Equiv.swap (0 : Fin 5) 3) reducedBarFiveDown reducedBarFiveLepton
    (-color) (-weak) permuteReducedWeight_swap03_barFiveDown
  rintro ⟨e, q⟩ he
  rw [eq_barFiveDown_of_normalizeWeight_eq e he]
  change
    q + blockCharge color weak
          (StandardSU5Orbit.permuteWeight (Equiv.swap (0 : Fin 5) 3)
            (StandardSU5Orbit.barFiveDown (e (Fin.last 4)))) - (-weak) =
      q + blockCharge color weak
          (StandardSU5Orbit.barFiveDown (e (Fin.last 4))) - (-color)
  rw [StandardSU5Orbit.permuteWeight_swap03_barFiveDown,
    blockCharge_barFiveLepton, blockCharge_barFiveDown]
  abel

/-!
## Raw characters of actual charged sources
-/

/-- Attach one source-sector charge to every raw Laurent monomial. -/
def rawResolvedWithOffset {A : Type*}
    (offset : A) (p : StandardAbelianCharge.RawCharacter) :
    RawResolvedCharacter A :=
  Finsupp.mapDomain (fun e => (e, offset)) p

theorem permuteRawResolved_rawResolvedWithOffset
    {A : Type*} (sigma : Equiv.Perm (Fin 5))
    (offset : A) (p : StandardAbelianCharge.RawCharacter) :
    permuteRawResolved sigma (rawResolvedWithOffset offset p) =
      rawResolvedWithOffset offset
        (Finsupp.mapDomain
          (StandardSU5Orbit.permuteWeight sigma) p) := by
  unfold permuteRawResolved rawResolvedWithOffset
  calc
    Finsupp.mapDomain (rawKeyPermEquiv sigma)
        (Finsupp.mapDomain (fun e => (e, offset)) p) =
      Finsupp.mapDomain
        (rawKeyPermEquiv sigma ∘ fun e => (e, offset)) p :=
          Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
        ((fun e => (e, offset)) ∘
          StandardSU5Orbit.permuteWeight sigma) p := by
      apply Finsupp.mapDomain_congr
      intro e _he
      rfl
    _ = Finsupp.mapDomain (fun e => (e, offset))
        (Finsupp.mapDomain
          (StandardSU5Orbit.permuteWeight sigma) p) :=
      Finsupp.mapDomain_comp

theorem rawResolvedWithOffset_isWeylInvariant
    {A : Type*} (offset : A)
    (p : StandardAbelianCharge.RawCharacter)
    (hp : StandardSU5Orbit.WeylInvariant p) :
    RawResolvedWeylInvariant (rawResolvedWithOffset offset p) := by
  intro sigma
  have hpSigma := hp sigma
  unfold StandardSU5Orbit.permute at hpSigma
  rw [permuteRawResolved_rawResolvedWithOffset, hpSigma]

/-- Raw charge-resolved contribution of one actual continuous-unitary source
summand. -/
def rawResolvedSummand {A : Type*}
    (s : StandardPhysicalSource.ChargedContinuousUnitarySummand A) :
    RawResolvedCharacter A :=
  s.coeff • rawResolvedWithOffset s.offset
    s.rep.ambientLaurentModel.poly

theorem rawResolvedSummand_isWeylInvariant
    {A : Type*}
    (s : StandardPhysicalSource.ChargedContinuousUnitarySummand A) :
    RawResolvedWeylInvariant (rawResolvedSummand s) := by
  have hBase : RawResolvedWeylInvariant
      (rawResolvedWithOffset s.offset s.rep.ambientLaurentModel.poly) :=
    rawResolvedWithOffset_isWeylInvariant s.offset
      s.rep.ambientLaurentModel.poly
      (standardWeylInvariant_of_ambient
        s.rep.ambientLaurentModel.poly
        s.rep.ambientLaurentModel.isWeylInvariant)
  intro sigma
  have hBaseSigma := hBase sigma
  unfold rawResolvedSummand permuteRawResolved at hBaseSigma ⊢
  rw [Finsupp.mapDomain_smul, hBaseSigma]

/-- Sum the raw charge-resolved characters before applying a block gauge
lift. -/
def rawResolvedSource {A : Type*} :
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource A →
      RawResolvedCharacter A
  | [] => 0
  | s :: source => rawResolvedSummand s + rawResolvedSource source

theorem rawResolvedSource_isWeylInvariant
    {A : Type*}
    (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource A) :
    RawResolvedWeylInvariant (rawResolvedSource source) := by
  induction source with
  | nil =>
      intro sigma
      simp [rawResolvedSource, permuteRawResolved]
  | cons s source ih =>
      intro sigma
      have hs := rawResolvedSummand_isWeylInvariant s sigma
      have hsource := ih sigma
      unfold permuteRawResolved at hsource
      unfold rawResolvedSource permuteRawResolved at hs ⊢
      rw [Finsupp.mapDomain_add, hs, hsource]

/-!
## The physical standard charge-orbit bridge-to-Abelian proton-operator neutrality conclusion
-/

@[simp]
theorem shiftProfile_single
    {A : Type*} [AddCommGroup A] (shift charge : A) (n : ℤ) :
    shiftProfile shift (Finsupp.single charge n) =
      Finsupp.single (charge + shift) n := by
  simp [shiftProfile]

/-- Remove the five field-dependent color/weak block charges from an observed
charge assignment.  No division, root, or choice of a `Y5/X` lift occurs. -/
def untwistCharges {A : Type*} [AddCommGroup A]
    (k : Charges A) (color weak : A) : Charges A where
  quark := k.quark - (color + weak)
  up := k.up - (color + color)
  down := k.down - (-color)
  lepton := k.lepton - (-weak)
  electron := k.electron - (weak + weak)

/-- Restoring the block charges after removing them recovers the observed
charge assignment. -/
theorem twistCharges_untwistCharges
    {A : Type*} [AddCommGroup A]
    (k : Charges A) (color weak : A) :
    twistCharges (untwistCharges k color weak) color weak = k := by
  ext <;> simp [twistCharges, untwistCharges] <;> abel

/-- Raw Weyl invariance and a pure physical SM profile imply the SU(5)-orbit
relations after the field-dependent block charges have been removed. -/
theorem untwistCharges_su5OrbitCompatible_of_pureSM
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A)
    (hSM : IsPureSMChargeSpectrum
      (blockResolved color weak p) generations k) :
    SU5OrbitCompatible (untwistCharges k color weak) := by
  have hQU := correctedTenQ_eq_tenUp color weak p hp
  have hQE := correctedTenQ_eq_tenElectron color weak p hp
  have hDL := correctedBarFiveDown_eq_barFiveLepton color weak p hp
  rw [correctedProjectedProfile_eq_shiftProfile,
    correctedProjectedProfile_eq_shiftProfile] at hQU hQE hDL
  rw [show chargeProfile (blockResolved color weak p) reducedTenQ =
      Finsupp.single k.quark generations from hSM.quark,
    show chargeProfile (blockResolved color weak p) reducedTenUp =
      Finsupp.single k.up generations from hSM.up,
    shiftProfile_single, shiftProfile_single] at hQU
  rw [show chargeProfile (blockResolved color weak p) reducedTenQ =
      Finsupp.single k.quark generations from hSM.quark,
    show chargeProfile (blockResolved color weak p) reducedTenElectron =
      Finsupp.single k.electron generations from hSM.electron,
    shiftProfile_single, shiftProfile_single] at hQE
  rw [show chargeProfile (blockResolved color weak p) reducedBarFiveDown =
      Finsupp.single k.down generations from hSM.down,
    show chargeProfile (blockResolved color weak p) reducedBarFiveLepton =
      Finsupp.single k.lepton generations from hSM.lepton,
    shiftProfile_single, shiftProfile_single] at hDL
  refine ⟨?_, ?_, ?_⟩
  · simpa [untwistCharges, sub_eq_add_neg] using
      Finsupp.single_left_injective hgenerations hQU
  · simpa [untwistCharges, sub_eq_add_neg] using
      Finsupp.single_left_injective hgenerations hQE
  · simpa [untwistCharges, sub_eq_add_neg] using
      Finsupp.single_left_injective hgenerations hDL

/-- Main algebraic theorem for an arbitrary standard block lift: an exact
physical SM charge profile makes both proton functionals neutral.  This is
the standard-branch `standard charge-orbit bridge -> Abelian proton-operator neutrality` route and uses no anomaly equation. -/
theorem proton_functionals_eq_zero_of_pureSM_blockResolved
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A)
    (hSM : IsPureSMChargeSpectrum
      (blockResolved color weak p) generations k) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  have hOrbit := untwistCharges_su5OrbitCompatible_of_pureSM
    color weak p hp generations hgenerations k hSM
  rw [← twistCharges_untwistCharges k color weak]
  exact proton_functionals_eq_zero_of_twist_of_su5OrbitCompatible
    (untwistCharges k color weak) color weak hOrbit

/-- A local exact-SM coefficient certificate supplies the pure-profile input
used by the preceding standard charge-orbit bridge theorem; gauge singlets are harmless. -/
theorem proton_functionals_eq_zero_of_exactSpectrum_blockResolved
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p)
    (generations : ℤ) (hgenerations : generations ≠ 0)
    (k : Charges A) (singlets : A →₀ ℤ)
    (hSpectrum : IsExactSMOnlyCoefficientSpectrum
      (blockResolved color weak p) generations k singlets) :
    protonFirst k = 0 ∧ protonSecond k = 0 := by
  apply proton_functionals_eq_zero_of_pureSM_blockResolved
    color weak p hp generations hgenerations k
  rw [hSpectrum.resolvedCharacter_eq]
  exact
    StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum
      generations k singlets

/-- Family-dependent form of the physical block-projection theorem.  If the
physical `Q` and `d^c` charge profiles are nonempty, there is a charge choice
supported by all five Standard Model field profiles for which both proton
functionals vanish.  No choice of integer lifts, roots of characters, or
anomaly equation is used. -/
theorem exists_supported_neutral_proton_sectors_blockResolved
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p : RawResolvedCharacter A)
    (hp : RawResolvedWeylInvariant p)
    (hTen : quarkProfile (blockResolved color weak p) ≠ 0)
    (hBarFive : downProfile (blockResolved color weak p) ≠ 0) :
    ∃ k : Charges A,
      ChargesSupported (blockResolved color weak p) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 := by
  let correctedQ :=
    correctedProjectedProfile color weak p reducedTenQ (color + weak)
  let correctedD :=
    correctedProjectedProfile color weak p reducedBarFiveDown (-color)
  have hCorrectedQ : correctedQ ≠ 0 := by
    change
      correctedProjectedProfile color weak p reducedTenQ (color + weak) ≠ 0
    rw [correctedProjectedProfile_eq_shiftProfile,
      shiftProfile_ne_zero_iff]
    exact hTen
  have hCorrectedD : correctedD ≠ 0 := by
    change
      correctedProjectedProfile color weak p reducedBarFiveDown (-color) ≠ 0
    rw [correctedProjectedProfile_eq_shiftProfile,
      shiftProfile_ne_zero_iff]
    exact hBarFive
  obtain ⟨q, hq⟩ :=
    StandardAbelianCharge.exists_apply_ne_zero_of_ne_zero
      correctedQ hCorrectedQ
  obtain ⟨r, hr⟩ :=
    StandardAbelianCharge.exists_apply_ne_zero_of_ne_zero
      correctedD hCorrectedD
  let external := StandardAbelianCharge.sectorCharges q r
  let k := twistCharges external color weak
  refine ⟨k, ?_, ?_⟩
  · have hQU := correctedTenQ_eq_tenUp color weak p hp
    have hQE := correctedTenQ_eq_tenElectron color weak p hp
    have hDL := correctedBarFiveDown_eq_barFiveLepton color weak p hp
    have hqQ :
        quarkProfile (blockResolved color weak p)
          (q + (color + weak)) ≠ 0 := by
      change
        correctedProjectedProfile color weak p reducedTenQ
            (color + weak) q ≠ 0 at hq
      rw [correctedProjectedProfile_eq_shiftProfile,
        shiftProfile_apply] at hq
      change
        chargeProfile (blockResolved color weak p) reducedTenQ
          (q + (color + weak)) ≠ 0
      simpa only [sub_neg_eq_add] using hq
    have hqU :
        upProfile (blockResolved color weak p)
          (q + (color + color)) ≠ 0 := by
      have hq' :
          correctedProjectedProfile color weak p reducedTenUp
              (color + color) q ≠ 0 := by
        rw [← hQU]
        exact hq
      rw [correctedProjectedProfile_eq_shiftProfile,
        shiftProfile_apply] at hq'
      change
        chargeProfile (blockResolved color weak p) reducedTenUp
          (q + (color + color)) ≠ 0
      simpa only [sub_neg_eq_add] using hq'
    have hqE :
        electronProfile (blockResolved color weak p)
          (q + (weak + weak)) ≠ 0 := by
      have hq' :
          correctedProjectedProfile color weak p reducedTenElectron
              (weak + weak) q ≠ 0 := by
        rw [← hQE]
        exact hq
      rw [correctedProjectedProfile_eq_shiftProfile,
        shiftProfile_apply] at hq'
      change
        chargeProfile (blockResolved color weak p) reducedTenElectron
          (q + (weak + weak)) ≠ 0
      simpa only [sub_neg_eq_add] using hq'
    have hrD :
        downProfile (blockResolved color weak p) (r - color) ≠ 0 := by
      change
        correctedProjectedProfile color weak p reducedBarFiveDown
            (-color) r ≠ 0 at hr
      rw [correctedProjectedProfile_eq_shiftProfile,
        shiftProfile_apply] at hr
      change chargeProfile (blockResolved color weak p)
        reducedBarFiveDown (r - color) ≠ 0
      simpa only [neg_neg] using hr
    have hrL :
        leptonProfile (blockResolved color weak p) (r - weak) ≠ 0 := by
      have hr' :
          correctedProjectedProfile color weak p reducedBarFiveLepton
              (-weak) r ≠ 0 := by
        rw [← hDL]
        exact hr
      rw [correctedProjectedProfile_eq_shiftProfile,
        shiftProfile_apply] at hr'
      change chargeProfile (blockResolved color weak p)
        reducedBarFiveLepton (r - weak) ≠ 0
      simpa only [neg_neg] using hr'
    change
      quarkProfile (blockResolved color weak p) k.quark ≠ 0 ∧
      upProfile (blockResolved color weak p) k.up ≠ 0 ∧
      downProfile (blockResolved color weak p) k.down ≠ 0 ∧
      leptonProfile (blockResolved color weak p) k.lepton ≠ 0 ∧
      electronProfile (blockResolved color weak p) k.electron ≠ 0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [k, external, StandardAbelianCharge.sectorCharges,
        twistCharges, add_assoc] using hqQ
    · simpa only [k, external, StandardAbelianCharge.sectorCharges,
        twistCharges, add_assoc] using hqU
    · simpa only [k, external, StandardAbelianCharge.sectorCharges,
        twistCharges] using hrD
    · simpa only [k, external, StandardAbelianCharge.sectorCharges,
        twistCharges] using hrL
    · simpa only [k, external, StandardAbelianCharge.sectorCharges,
        twistCharges, add_assoc] using hqE
  · simpa [k] using
      (proton_functionals_eq_zero_of_twist_of_su5OrbitCompatible
        external color weak
        (StandardAbelianCharge.sectorCharges_su5OrbitCompatible q r))

/-!
## Actual common-gauge sources
-/

/-- The charge-resolved character obtained by adding an actual common
centralizing block-gauge lift to all external character sectors. -/
def actualBlockResolvedCharacter
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (matter : CommonGaugeSource H gauge) :
    ResolvedCharacter (ChargeLabel H) :=
  let blockGauge := actualBlockGaugeHom iota W gauge hCentral
  blockResolved (colorCharge blockGauge) (weakCharge blockGauge)
    (rawResolvedSource matter.toChargedSource)

/-!
### Strict ordinary Abelian specialization

An ordinary internal symmetry commutes with all of `SU(6)`, so the preceding
common-gauge construction has the identity lift.  This specialization keeps
the actual character-sector decomposition of every finite-dimensional
summand while eliminating any independent gauge-lift assumption.
-/

/-- The canonical identity lift centralizes every standard-branch embedding. -/
theorem identityGauge_centralizes
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6) :
    ∀ h, (1 : H →* CompactEmbeddingClassification.SU6) h ∈
      PhysicalCentralizer iota := by
  intro h
  change (1 : CompactEmbeddingClassification.SU6) ∈ PhysicalCentralizer iota
  exact Subgroup.one_mem _

/-- Extracting block coefficients from the identity lift gives the identity
homomorphism into the compact block centralizer. -/
theorem actualBlockGaugeHom_identity
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    actualBlockGaugeHom iota W
        (1 : H →* CompactEmbeddingClassification.SU6)
        (identityGauge_centralizes iota) = 1 := by
  apply MonoidHom.ext
  intro h
  change
    (compactBlockCoefficientHom iota W)
        ((toPhysicalCentralizerHom iota
          (1 : H →* CompactEmbeddingClassification.SU6)
          (identityGauge_centralizes iota)) h) = 1
  have hLift :
      (toPhysicalCentralizerHom iota
        (1 : H →* CompactEmbeddingClassification.SU6)
        (identityGauge_centralizes iota)) h = 1 := by
    apply Subtype.ext
    rfl
  rw [hLift, map_one]

/-- The identity lift has trivial color charge. -/
theorem colorCharge_actualBlockGaugeHom_identity
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    colorCharge
        (actualBlockGaugeHom iota W
          (1 : H →* CompactEmbeddingClassification.SU6)
          (identityGauge_centralizes iota)) = 0 := by
  rw [actualBlockGaugeHom_identity]
  ext h
  rfl

/-- The identity lift has trivial weak charge. -/
theorem weakCharge_actualBlockGaugeHom_identity
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    weakCharge
        (actualBlockGaugeHom iota W
          (1 : H →* CompactEmbeddingClassification.SU6)
          (identityGauge_centralizes iota)) = 0 := by
  rw [actualBlockGaugeHom_identity]
  ext h
  rfl

/-- Charge-resolved character of a finite virtual source carrying a strict
ordinary Abelian action commuting with the full `SU(6)` representation. -/
def ordinaryAbelianResolvedCharacter
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (matter : OrdinaryAbelianSource H) :
    ResolvedCharacter (ChargeLabel H) :=
  actualBlockResolvedCharacter iota W
    (1 : H →* CompactEmbeddingClassification.SU6)
    (identityGauge_centralizes iota) matter.toCommonGaugeSource

/-- Physical-source form of the family-dependent standard charge-orbit bridge-to-Abelian proton-operator neutrality theorem.  Once a
common centralizing gauge lift has produced the actual block-resolved
character, nonempty physical `Q` and `d^c` profiles force a supported charge
choice on which both proton functionals vanish. -/
theorem actualBlockResolvedCharacter_exists_supported_neutral_proton_sectors
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (matter : CommonGaugeSource H gauge)
    (hTen : quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (actualBlockResolvedCharacter iota W gauge hCentral matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 := by
  let blockGauge := actualBlockGaugeHom iota W gauge hCentral
  change
    quarkProfile
        (blockResolved (colorCharge blockGauge) (weakCharge blockGauge)
          (rawResolvedSource matter.toChargedSource)) ≠ 0 at hTen
  change
    downProfile
        (blockResolved (colorCharge blockGauge) (weakCharge blockGauge)
          (rawResolvedSource matter.toChargedSource)) ≠ 0 at hBarFive
  change
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (blockResolved (colorCharge blockGauge) (weakCharge blockGauge)
            (rawResolvedSource matter.toChargedSource)) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0
  exact exists_supported_neutral_proton_sectors_blockResolved
    (colorCharge blockGauge) (weakCharge blockGauge)
    (rawResolvedSource matter.toChargedSource)
    (rawResolvedSource_isWeylInvariant matter.toChargedSource)
    hTen hBarFive

/-- Explicit finite-Abelian specialization of the physical-source profile
theorem. -/
theorem finiteAbelian_actualBlockResolvedCharacter_exists_supported_neutral_proton_sectors
    {H : Type u} [CommGroup H] [Finite H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (matter : CommonGaugeSource H gauge)
    (hTen : quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (actualBlockResolvedCharacter iota W gauge hCentral matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  actualBlockResolvedCharacter_exists_supported_neutral_proton_sectors
    iota W gauge hCentral matter hTen hBarFive

/-- standard charge-orbit bridge-to-Abelian proton-operator neutrality at profile level for a strict ordinary Abelian source.  The
supported sectors come from the actual simultaneous character decomposition
of the supplied actions; no gauge lift, anomaly equation, or charge-group
divisibility is assumed. -/
theorem ordinaryAbelianResolvedCharacter_exists_supported_neutral_proton_sectors
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (matter : OrdinaryAbelianSource H)
    (hTen : quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported (ordinaryAbelianResolvedCharacter iota W matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  actualBlockResolvedCharacter_exists_supported_neutral_proton_sectors
    iota W (1 : H →* CompactEmbeddingClassification.SU6)
    (identityGauge_centralizes iota) matter.toCommonGaugeSource hTen hBarFive

/-- Explicit finite-Abelian specialization of the strict ordinary source
theorem.  Character collisions are retained by the same `Finsupp` model. -/
theorem finiteAbelian_ordinaryAbelianResolvedCharacter_exists_supported_neutral_proton_sectors
    {H : Type u} [CommGroup H] [Finite H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (matter : OrdinaryAbelianSource H)
    (hTen : quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported (ordinaryAbelianResolvedCharacter iota W matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  ordinaryAbelianResolvedCharacter_exists_supported_neutral_proton_sectors
    iota W matter hTen hBarFive

/-- A physical standard-branch source whose exact chiral spectrum is read
from the raw hypercharge character rigidity weights after applying its actual common block-gauge lift.
The residual group is an arbitrary Abelian group; finite character collisions
are part of `actualBlockResolvedCharacter` itself. -/
structure PureSMActualBlockProjectedSource
    (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : WeakDoubletData (euclideanDefiningRestriction iota)
  gauge : H →* CompactEmbeddingClassification.SU6
  gauge_centralizes : ∀ h, gauge h ∈ PhysicalCentralizer iota
  matter : CommonGaugeSource H gauge
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  spectrum : IsExactSMOnlyCoefficientSpectrum
    (actualBlockResolvedCharacter iota weakDoubletData gauge
      gauge_centralizes matter)
    generations physicalCharges singlets

namespace PureSMActualBlockProjectedSource

variable {H : Type u} [CommGroup H]

def blockGauge (S : PureSMActualBlockProjectedSource H) :
    H →* CompactBlockCentralizer.Group :=
  actualBlockGaugeHom S.iota S.weakDoubletData S.gauge
    S.gauge_centralizes

def color (S : PureSMActualBlockProjectedSource H) : ChargeLabel H :=
  colorCharge S.blockGauge

def weak (S : PureSMActualBlockProjectedSource H) : ChargeLabel H :=
  weakCharge S.blockGauge

def rawCharacter (S : PureSMActualBlockProjectedSource H) :
    RawResolvedCharacter (ChargeLabel H) :=
  rawResolvedSource S.matter.toChargedSource

theorem actualBlockResolvedCharacter_eq (S : PureSMActualBlockProjectedSource H) :
    actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter =
      blockResolved S.color S.weak S.rawCharacter :=
  rfl

theorem rawCharacter_isWeylInvariant
    (S : PureSMActualBlockProjectedSource H) :
    RawResolvedWeylInvariant S.rawCharacter :=
  rawResolvedSource_isWeylInvariant S.matter.toChargedSource

theorem pureSMChargeSpectrum (S : PureSMActualBlockProjectedSource H) :
    IsPureSMChargeSpectrum
      (blockResolved S.color S.weak S.rawCharacter)
      S.generations S.physicalCharges := by
  rw [← S.actualBlockResolvedCharacter_eq,
    S.spectrum.resolvedCharacter_eq]
  exact
    StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum
      S.generations S.physicalCharges S.singlets

theorem quarkProfile_ne_zero (S : PureSMActualBlockProjectedSource H) :
    quarkProfile (blockResolved S.color S.weak S.rawCharacter) ≠ 0 := by
  rw [S.pureSMChargeSpectrum.quark]
  exact Finsupp.single_ne_zero.mpr S.generations_ne

theorem downProfile_ne_zero (S : PureSMActualBlockProjectedSource H) :
    downProfile (blockResolved S.color S.weak S.rawCharacter) ≠ 0 := by
  rw [S.pureSMChargeSpectrum.down]
  exact Finsupp.single_ne_zero.mpr S.generations_ne

/-- The exact physical source also satisfies the family-dependent standard charge-orbit bridge
conclusion: it contains a supported charge choice for which both proton
functionals vanish.  This formulation does not identify families by a single
universal charge. -/
theorem exists_supported_neutral_proton_sectors
    (S : PureSMActualBlockProjectedSource H) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
            S.gauge_centralizes S.matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 := by
  rw [S.actualBlockResolvedCharacter_eq]
  exact exists_supported_neutral_proton_sectors_blockResolved
    S.color S.weak S.rawCharacter S.rawCharacter_isWeylInvariant
    S.quarkProfile_ne_zero S.downProfile_ne_zero

/-- Explicit finite-Abelian specialization of the supported-sector theorem.
Finite character collisions have already been summed in the projected
character. -/
theorem finiteAbelian_exists_supported_neutral_proton_sectors
    [Finite H] (S : PureSMActualBlockProjectedSource H) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
            S.gauge_centralizes S.matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  S.exists_supported_neutral_proton_sectors

/-- standard charge-orbit bridge gives the three SU(5)-orbit relations for the physical charges after
the actual color/weak block contribution is removed. -/
theorem untwistedCharge_equalities
    (S : PureSMActualBlockProjectedSource H) :
    SU5OrbitCompatible
      (untwistCharges S.physicalCharges S.color S.weak) :=
  untwistCharges_su5OrbitCompatible_of_pureSM
    S.color S.weak S.rawCharacter S.rawCharacter_isWeylInvariant
    S.generations S.generations_ne S.physicalCharges
    S.pureSMChargeSpectrum

/-- Main arbitrary-Abelian standard-branch source conclusion.  It is the
physical coefficient bridge `standard charge-orbit bridge` composed with the algebraic proton lemma
`Abelian proton-operator neutrality`, independently of continuous anomaly cancellation. -/
theorem proton_functionals_eq_zero
    (S : PureSMActualBlockProjectedSource H) :
    protonFirst S.physicalCharges = 0 ∧
      protonSecond S.physicalCharges = 0 :=
  proton_functionals_eq_zero_of_pureSM_blockResolved
    S.color S.weak S.rawCharacter S.rawCharacter_isWeylInvariant
    S.generations S.generations_ne S.physicalCharges
    S.pureSMChargeSpectrum

theorem protonCharacters_eq_one
    (S : PureSMActualBlockProjectedSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 := by
  obtain ⟨hFirst, hSecond⟩ := S.proton_functionals_eq_zero
  exact ⟨protonFirstCharacter_eq_one_of_eq_zero _ hFirst,
    protonSecondCharacter_eq_one_of_eq_zero _ hSecond⟩

theorem protonPhases_eq_one
    (S : PureSMActualBlockProjectedSource H) (h : H) :
    protonFirstCharacter S.physicalCharges h = 1 ∧
      protonSecondCharacter S.physicalCharges h = 1 := by
  obtain ⟨hFirst, hSecond⟩ := S.protonCharacters_eq_one
  exact ⟨congrArg (fun chi : H →* Circle => chi h) hFirst,
    congrArg (fun chi : H →* Circle => chi h) hSecond⟩

/-- Explicit finite-Abelian specialization.  No roots or divisibility in the
finite character group are assumed. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : PureSMActualBlockProjectedSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 :=
  S.protonCharacters_eq_one

end PureSMActualBlockProjectedSource

/-!
## Exact strict ordinary Abelian sources

This is the standard charge-orbit bridge physical-source interface specialized to ordinary Abelian
internal symmetries.  Its matter data are actual finite-dimensional
continuous-unitary `SU(6)` representations with commuting unitary Abelian
actions.  The spectrum certificate identifies their computed, charge-resolved
finite-weight character with the intended chiral SM target.
-/

/-- Exact SM coefficient data obtained from a strict ordinary Abelian action
on a finite virtual `SU(6)` source. -/
structure PureSMOrdinaryAbelianProjectedSource
    (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : WeakDoubletData (euclideanDefiningRestriction iota)
  matter : OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  spectrum : IsExactSMOnlyCoefficientSpectrum
    (ordinaryAbelianResolvedCharacter iota weakDoubletData matter)
    generations physicalCharges singlets

namespace PureSMOrdinaryAbelianProjectedSource

variable {H : Type u} [CommGroup H]

/-- Forget that the common lift was constructed canonically.  This embeds the
strict ordinary source into the more general gauge-twisted standard charge-orbit bridge interface. -/
def toActualBlockProjectedSource
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    PureSMActualBlockProjectedSource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  gauge := 1
  gauge_centralizes := identityGauge_centralizes S.iota
  matter := S.matter.toCommonGaugeSource
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  spectrum := S.spectrum

@[simp]
theorem toActualBlockProjectedSource_color
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    S.toActualBlockProjectedSource.color = 0 :=
  colorCharge_actualBlockGaugeHom_identity S.iota S.weakDoubletData

@[simp]
theorem toActualBlockProjectedSource_weak
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    S.toActualBlockProjectedSource.weak = 0 :=
  weakCharge_actualBlockGaugeHom_identity S.iota S.weakDoubletData

/-- standard charge-orbit bridge in its direct strict-ordinary form:
`k_Q = k_u = k_e` and `k_d = k_L` for the physical residual charges. -/
theorem physicalCharge_equalities
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    SU5OrbitCompatible S.physicalCharges := by
  have hOrbit := S.toActualBlockProjectedSource.untwistedCharge_equalities
  change
    SU5OrbitCompatible
      (untwistCharges S.physicalCharges
        S.toActualBlockProjectedSource.color
        S.toActualBlockProjectedSource.weak) at hOrbit
  rw [S.toActualBlockProjectedSource_color,
    S.toActualBlockProjectedSource_weak] at hOrbit
  simpa [untwistCharges] using hOrbit

theorem quark_eq_up
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    S.physicalCharges.quark = S.physicalCharges.up :=
  S.physicalCharge_equalities.1

theorem quark_eq_electron
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    S.physicalCharges.quark = S.physicalCharges.electron :=
  S.physicalCharge_equalities.2.1

theorem down_eq_lepton
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    S.physicalCharges.down = S.physicalCharges.lepton :=
  S.physicalCharge_equalities.2.2

/-- The exact ordinary source contains a supported charge assignment on
which both proton charge functionals vanish. -/
theorem exists_supported_neutral_proton_sectors
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    ∃ k : Charges (ChargeLabel H),
      ChargesSupported
          (ordinaryAbelianResolvedCharacter
            S.iota S.weakDoubletData S.matter) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  S.toActualBlockProjectedSource.exists_supported_neutral_proton_sectors

/-- Main arbitrary-Abelian standard charge-orbit bridge-to-Abelian proton-operator neutrality conclusion for strict ordinary internal
symmetries.  It is independent of continuous anomaly cancellation. -/
theorem proton_functionals_eq_zero
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    protonFirst S.physicalCharges = 0 ∧
      protonSecond S.physicalCharges = 0 :=
  S.toActualBlockProjectedSource.proton_functionals_eq_zero

theorem protonCharacters_eq_one
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 :=
  S.toActualBlockProjectedSource.protonCharacters_eq_one

theorem protonPhases_eq_one
    (S : PureSMOrdinaryAbelianProjectedSource H) (h : H) :
    protonFirstCharacter S.physicalCharges h = 1 ∧
      protonSecondCharacter S.physicalCharges h = 1 :=
  S.toActualBlockProjectedSource.protonPhases_eq_one h

/-- Finite Abelian specialization of the exact ordinary-source theorem. -/
theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : PureSMOrdinaryAbelianProjectedSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 :=
  S.protonCharacters_eq_one

end PureSMOrdinaryAbelianProjectedSource

end
end StandardBlockChargeProjection
end GUT
