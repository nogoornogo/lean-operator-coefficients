import GUT.SU6.SelectionRules.Models.OrdinaryAbelianAmbientModel
import GUT.SU6.SelectionRules.StandardBranch.StandardBlockChargeProjection
import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalCharacterBridge
import Mathlib.Tactic

open Physics

open Math

/-!
# Charge-resolved physical-torus characters

This file gives the hypercharge character rigidity and standard charge-orbit bridge source bridges one common finite normal form.
For an arbitrary physical hypercharge cocharacter `(m,n)`, every ambient
`SU(6)` weight is restricted to the integral physical four-torus and paired
with the character of its strict ordinary Abelian eigensector.

Forgetting the Abelian label recovers the actual hypercharge character rigidity Laurent restriction.
At the standard pair `(-2,3)`, the same normal form is the injective image of
the normalized standard charge-orbit bridge character.  Consequently one exact charge-resolved
SM-plus-singlets spectrum certificate supplies both inputs without assuming
two unrelated character equalities.
-/

namespace GUT
namespace PhysicalChargeResolvedBridge

open scoped BigOperators

open FiniteAbelianChargeSectors
open PhysicalTorusCharacterBridge
open StandardAbelianCharge
open StandardBlockChargeProjection
open StandardBranchProtonObstruction
open StandardPhysicalSource
open StandardSMCharacterTarget

noncomputable section

universe u

abbrev PhysicalResolvedKey (A : Type*) := PhysicalExponent × A
abbrev PhysicalResolvedCharacter (A : Type*) :=
  PhysicalResolvedKey A →₀ ℤ

/-!
## Restriction of an actual charged source
-/

/-- Restrict one ambient weight and retain its independent Abelian sector
label. -/
def physicalProjectKey {A : Type*}
    (m n : ℤ) (offset : A) (e : AmbientWeightLattice.Exponent) :
    PhysicalResolvedKey A :=
  (restrictExponent m n e, offset)

/-- The contribution of one actual continuous-unitary charged summand. -/
def summandPhysicalResolvedCharacter {A : Type*} [AddCommGroup A]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand A) :
    PhysicalResolvedCharacter A :=
  s.coeff • Finsupp.mapDomain (physicalProjectKey m n s.offset)
    s.rep.ambientLaurentModel.poly

/-- The physical-torus and Abelian-charge resolved character of a finite
actual source. -/
def sourcePhysicalResolvedCharacter {A : Type*} [AddCommGroup A]
    (m n : ℤ) : FiniteChargedContinuousUnitarySource A →
      PhysicalResolvedCharacter A
  | [] => 0
  | s :: source =>
      summandPhysicalResolvedCharacter m n s +
        sourcePhysicalResolvedCharacter m n source

/-- Forget the Abelian label, summing all colliding charge sectors. -/
def forgetCharge {A : Type*}
    (p : PhysicalResolvedCharacter A) : IntegralPhysicalCharacter :=
  Finsupp.mapDomain Prod.fst p

theorem forgetCharge_add {A : Type*}
    (p q : PhysicalResolvedCharacter A) :
    forgetCharge (p + q) = forgetCharge p + forgetCharge q :=
  Finsupp.mapDomain_add

theorem ambient_zscale_eq_zsmul
    (k : ℤ) (p : AmbientWeightLattice.Character) :
    AmbientLaurent.zscale k p = k • p := by
  ext e
  simp [AmbientLaurent.zscale]

theorem forgetCharge_summandPhysicalResolvedCharacter
    {A : Type*} [AddCommGroup A]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand A) :
    forgetCharge (summandPhysicalResolvedCharacter m n s) =
      restrictIntegralCharacter m n
        (AmbientLaurent.zscale s.coeff
          s.rep.ambientLaurentModel.poly) := by
  unfold forgetCharge summandPhysicalResolvedCharacter
  rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_comp.symm]
  have hKey :
      Finsupp.mapDomain
          (Prod.fst ∘ physicalProjectKey m n s.offset)
          s.rep.ambientLaurentModel.poly =
        Finsupp.mapDomain (restrictExponent m n)
          s.rep.ambientLaurentModel.poly := by
    apply Finsupp.mapDomain_congr
    intro e _he
    rfl
  rw [hKey, ambient_zscale_eq_zsmul, restrictIntegralCharacter,
    Finsupp.mapDomain_smul]

/-- Forgetting charges from the common resolved source gives exactly the
restriction of its checked ambient Laurent model. -/
theorem forgetCharge_sourcePhysicalResolvedCharacter
    {A : Type*} [AddCommGroup A]
    (m n : ℤ) (source : FiniteChargedContinuousUnitarySource A) :
    forgetCharge (sourcePhysicalResolvedCharacter m n source) =
      restrictIntegralCharacter m n
        (FiniteChargedContinuousUnitarySource.ambientLaurentModel
          source).poly := by
  induction source with
  | nil =>
      rfl
  | cons s source ih =>
      change
        forgetCharge
            (summandPhysicalResolvedCharacter m n s +
              sourcePhysicalResolvedCharacter m n source) =
          restrictIntegralCharacter m n
            (AmbientLaurent.zscale s.coeff
                s.rep.ambientLaurentModel.poly +
              (FiniteChargedContinuousUnitarySource.ambientLaurentModel
                source).poly)
      rw [forgetCharge_add,
        forgetCharge_summandPhysicalResolvedCharacter, ih]
      unfold restrictIntegralCharacter
      exact Finsupp.mapDomain_add.symm

/-!
## The single exact physical spectrum target
-/

def physicalSMResolvedKey {A : Type*}
    (charges : Charges A) (i : Fin 15) : PhysicalResolvedKey A :=
  (smExponent i, smCharge charges i)

def exactSMResolvedCharacter {A : Type*}
    (generations : ℤ) (charges : Charges A) :
    PhysicalResolvedCharacter A :=
  ∑ i : Fin 15,
    Finsupp.single (physicalSMResolvedKey charges i) generations

def singletResolvedCharacter {A : Type*}
    (singlets : A →₀ ℤ) : PhysicalResolvedCharacter A :=
  Finsupp.mapDomain (fun q => ((0 : PhysicalExponent), q)) singlets

def exactSMWithSingletsResolvedCharacter {A : Type*}
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) :
    PhysicalResolvedCharacter A :=
  exactSMResolvedCharacter generations charges +
    singletResolvedCharacter singlets

/-- Net chiral singlet multiplicity after forgetting the residual charge. -/
def totalSingletMultiplicity {A : Type*} (singlets : A →₀ ℤ) : ℤ :=
  singlets.sum fun _ multiplicity => multiplicity

/-!
### Local coefficient formulation
-/

theorem smExponent_injective :
    Function.Injective PhysicalTorusCharacterBridge.smExponent := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [PhysicalTorusCharacterBridge.smExponent]

theorem physicalSMResolvedKey_injective
    {A : Type*} (charges : Charges A) :
    Function.Injective (physicalSMResolvedKey charges) := by
  intro i j hij
  apply smExponent_injective
  exact congrArg Prod.fst hij

theorem smExponent_ne_zero (i : Fin 15) :
    PhysicalTorusCharacterBridge.smExponent i ≠ 0 := by
  fin_cases i <;> decide

theorem zeroPhysicalWeightKey_injective {A : Type*} :
    Function.Injective
      (fun q : A => ((0 : PhysicalExponent), q)) := by
  intro q r h
  exact congrArg Prod.snd h

@[simp]
theorem singletResolvedCharacter_apply_zero
    {A : Type*} (singlets : A →₀ ℤ) (q : A) :
    singletResolvedCharacter singlets ((0 : PhysicalExponent), q) =
      singlets q := by
  exact Finsupp.mapDomain_apply_of_injective zeroPhysicalWeightKey_injective singlets q

theorem exactSMResolvedCharacter_apply_physicalSMResolvedKey
    {A : Type*} (generations : ℤ) (charges : Charges A) (i : Fin 15) :
    exactSMResolvedCharacter generations charges
        (physicalSMResolvedKey charges i) = generations := by
  classical
  simp [exactSMResolvedCharacter, Finsupp.single_apply,
    (physicalSMResolvedKey_injective charges).eq_iff]

theorem exactSMResolvedCharacter_apply_of_notMem_range
    {A : Type*} (generations : ℤ) (charges : Charges A)
    (key : PhysicalResolvedKey A)
    (hkey : key ∉ Set.range (physicalSMResolvedKey charges)) :
    exactSMResolvedCharacter generations charges key = 0 := by
  classical
  have hne : ∀ i : Fin 15, physicalSMResolvedKey charges i ≠ key := by
    intro i hi
    exact hkey ⟨i, hi⟩
  simp [exactSMResolvedCharacter, hne]

theorem singletResolvedCharacter_apply_of_weight_ne_zero
    {A : Type*} (singlets : A →₀ ℤ)
    {weight : PhysicalExponent} (hWeight : weight ≠ 0) (q : A) :
    singletResolvedCharacter singlets (weight, q) = 0 := by
  rw [singletResolvedCharacter, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨r, hr⟩
  exact hWeight (congrArg Prod.fst hr).symm

/-- Local exact-SM chiral-index data in the common hypercharge character rigidity/standard charge-orbit bridge normal form. -/
structure IsExactSMOnlyPhysicalCoefficientSpectrum
    {A : Type*} (p : PhysicalResolvedCharacter A)
    (generations : ℤ) (charges : Charges A)
    (singlets : A →₀ ℤ) : Prop where
  smMultiplicity : ∀ i : Fin 15,
    p (physicalSMResolvedKey charges i) = generations
  singletMultiplicity : ∀ q : A,
    p ((0 : PhysicalExponent), q) = singlets q
  noExoticNonSinglets : ∀ key : PhysicalResolvedKey A,
    key.1 ≠ 0 → key ∉ Set.range (physicalSMResolvedKey charges) →
      p key = 0

namespace IsExactSMOnlyPhysicalCoefficientSpectrum

variable {A : Type*} {p : PhysicalResolvedCharacter A}
  {generations : ℤ} {charges : Charges A} {singlets : A →₀ ℤ}

/-- The local physical multiplicities determine the single exact resolved
character used by both hypercharge character rigidity and standard charge-orbit bridge. -/
theorem resolvedCharacter_eq
    (hSpectrum : IsExactSMOnlyPhysicalCoefficientSpectrum
      p generations charges singlets) :
    p = exactSMWithSingletsResolvedCharacter
      generations charges singlets := by
  classical
  ext key
  rcases key with ⟨weight, q⟩
  by_cases hWeight : weight = 0
  · subst weight
    have hNotSM :
        ((0 : PhysicalExponent), q) ∉
          Set.range (physicalSMResolvedKey charges) := by
      rintro ⟨i, hi⟩
      exact smExponent_ne_zero i (congrArg Prod.fst hi)
    rw [hSpectrum.singletMultiplicity]
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations charges ((0 : PhysicalExponent), q) hNotSM,
      singletResolvedCharacter_apply_zero]
    exact (zero_add _).symm
  · by_cases hSM :
        (weight, q) ∈ Set.range (physicalSMResolvedKey charges)
    · rcases hSM with ⟨i, hi⟩
      rw [← hi, hSpectrum.smMultiplicity]
      simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
      rw [exactSMResolvedCharacter_apply_physicalSMResolvedKey]
      change generations = generations +
        singletResolvedCharacter singlets
          (PhysicalTorusCharacterBridge.smExponent i,
            StandardSMCharacterTarget.smCharge charges i)
      rw [singletResolvedCharacter_apply_of_weight_ne_zero
        singlets (smExponent_ne_zero i)]
      exact (add_zero _).symm
    · rw [hSpectrum.noExoticNonSinglets (weight, q) hWeight hSM]
      simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
      rw [exactSMResolvedCharacter_apply_of_notMem_range
        generations charges (weight, q) hSM,
        singletResolvedCharacter_apply_of_weight_ne_zero
          singlets hWeight]
      exact (zero_add _).symm

/-- Equality with the canonical target exposes the corresponding local
coefficient data. -/
theorem of_resolvedCharacter_eq
    (h : p = exactSMWithSingletsResolvedCharacter
      generations charges singlets) :
    IsExactSMOnlyPhysicalCoefficientSpectrum
      p generations charges singlets := by
  classical
  rw [h]
  constructor
  · intro i
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_physicalSMResolvedKey]
    change generations +
      singletResolvedCharacter singlets
        (PhysicalTorusCharacterBridge.smExponent i,
          StandardSMCharacterTarget.smCharge charges i) = generations
    rw [singletResolvedCharacter_apply_of_weight_ne_zero
      singlets (smExponent_ne_zero i)]
    exact add_zero _
  · intro q
    have hNotSM :
        ((0 : PhysicalExponent), q) ∉
          Set.range (physicalSMResolvedKey charges) := by
      rintro ⟨i, hi⟩
      exact smExponent_ne_zero i (congrArg Prod.fst hi)
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations charges ((0 : PhysicalExponent), q) hNotSM,
      singletResolvedCharacter_apply_zero]
    exact zero_add _
  · intro key hWeight hNotSM
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations charges key hNotSM,
      singletResolvedCharacter_apply_of_weight_ne_zero
        singlets hWeight]
    exact zero_add 0

theorem iff_resolvedCharacter_eq :
    IsExactSMOnlyPhysicalCoefficientSpectrum
        p generations charges singlets ↔
      p = exactSMWithSingletsResolvedCharacter
        generations charges singlets :=
  ⟨resolvedCharacter_eq, of_resolvedCharacter_eq⟩

end IsExactSMOnlyPhysicalCoefficientSpectrum

theorem mapDomain_const_zero
    {A : Type*} [AddCommGroup A] (singlets : A →₀ ℤ) :
    Finsupp.mapDomain (fun _ : A => (0 : PhysicalExponent)) singlets =
      Finsupp.single 0 (totalSingletMultiplicity singlets) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    rw [Finsupp.mapDomain_apply_eq_sum
      (fun _ : A => (0 : PhysicalExponent)) singlets (a := (0 : A))]
    simp [totalSingletMultiplicity, Finsupp.sum]
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp [he]
    · rintro ⟨q, hq⟩
      exact he hq.symm

theorem physical_zscale_eq_zsmul
    (k : ℤ) (p : IntegralPhysicalCharacter) :
    PhysicalTorusCharacterBridge.zscale k p = k • p := by
  ext e
  simp [PhysicalTorusCharacterBridge.zscale]

theorem forgetCharge_exactSMResolvedCharacter
    {A : Type*} [AddCommGroup A]
    (generations : ℤ) (charges : Charges A) :
    forgetCharge (exactSMResolvedCharacter generations charges) =
      zscale generations integralSMCharacter := by
  classical
  unfold forgetCharge exactSMResolvedCharacter integralSMCharacter
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, physicalSMResolvedKey]
  rw [physical_zscale_eq_zsmul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

theorem forgetCharge_singletResolvedCharacter
    {A : Type*} [AddCommGroup A] (singlets : A →₀ ℤ) :
    forgetCharge (singletResolvedCharacter singlets) =
      integralSingletCharacter (totalSingletMultiplicity singlets) := by
  unfold forgetCharge singletResolvedCharacter
  calc
    Finsupp.mapDomain Prod.fst
        (Finsupp.mapDomain
          (fun q => ((0 : PhysicalExponent), q)) singlets) =
        Finsupp.mapDomain
          (Prod.fst ∘ fun q => ((0 : PhysicalExponent), q)) singlets :=
      Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          (fun _ : A => (0 : PhysicalExponent)) singlets := by
      apply Finsupp.mapDomain_congr
      intro q _hq
      rfl
    _ = integralSingletCharacter
          (totalSingletMultiplicity singlets) := by
      rw [mapDomain_const_zero]
      rfl

theorem forgetCharge_exactSMWithSingletsResolvedCharacter
    {A : Type*} [AddCommGroup A]
    (generations : ℤ) (charges : Charges A)
    (singlets : A →₀ ℤ) :
    forgetCharge
        (exactSMWithSingletsResolvedCharacter
          generations charges singlets) =
      exactSMCharacter generations
        (totalSingletMultiplicity singlets) := by
  rw [PhysicalChargeResolvedBridge.exactSMWithSingletsResolvedCharacter,
    forgetCharge_add, forgetCharge_exactSMResolvedCharacter,
    forgetCharge_singletResolvedCharacter]
  rfl

/-!
## Compatibility with the normalized standard-branch character
-/

/-- Embed a normalized standard charge-orbit bridge key into the physical four-torus character
lattice at the standard hypercharge pair. -/
def standardKeyEmbedding {A : Type*}
    (key : StandardAbelianCharge.ResolvedKey A) : PhysicalResolvedKey A :=
  (StandardSMCharacterTarget.standardExponent key.1, key.2)

theorem standardKeyEmbedding_injective {A : Type*} :
    Function.Injective (standardKeyEmbedding (A := A)) := by
  rintro ⟨w, q⟩ ⟨v, r⟩ h
  change
    (StandardSMCharacterTarget.standardExponent w, q) =
      (StandardSMCharacterTarget.standardExponent v, r) at h
  have hParts :
      StandardSMCharacterTarget.standardExponent w =
          StandardSMCharacterTarget.standardExponent v ∧
        q = r := by
    simpa only [Prod.mk.injEq] using h
  rcases hParts with ⟨hWeight, hCharge⟩
  exact Prod.ext
    (StandardSMCharacterTarget.standardExponent_injective hWeight)
    hCharge

def embedStandardCharacter {A : Type*}
    (p : StandardAbelianCharge.ResolvedCharacter A) :
    PhysicalResolvedCharacter A :=
  Finsupp.mapDomain standardKeyEmbedding p

theorem embedStandardCharacter_injective {A : Type*} :
    Function.Injective (embedStandardCharacter (A := A)) :=
  Finsupp.mapDomain_injective (M := ℤ) standardKeyEmbedding_injective

theorem embedStandardCharacter_add {A : Type*}
    (p q : StandardAbelianCharge.ResolvedCharacter A) :
    embedStandardCharacter (p + q) =
      embedStandardCharacter p + embedStandardCharacter q :=
  Finsupp.mapDomain_add

theorem summandPhysicalResolvedCharacter_standard
    {A : Type*} [AddCommGroup A]
    (s : ChargedContinuousUnitarySummand A) :
    summandPhysicalResolvedCharacter (-2) 3 s =
      embedStandardCharacter
        (s.toModeled.resolved (0 : ℤ →+ A)) := by
  unfold summandPhysicalResolvedCharacter embedStandardCharacter
    ChargedContinuousUnitarySummand.toModeled
    ChargedModeledVirtualSummand.resolved
    StandardPhysicalSource.chargeResolvedWithOffset
  rw [Finsupp.mapDomain_smul]
  congr 1
  calc
    Finsupp.mapDomain (physicalProjectKey (-2) 3 s.offset)
        s.rep.ambientLaurentModel.poly =
      Finsupp.mapDomain
          (standardKeyEmbedding ∘
            affineProjectKey (0 : ℤ →+ A) s.offset)
          s.rep.ambientLaurentModel.poly := by
        apply Finsupp.mapDomain_congr
        intro e _he
        apply Prod.ext
        · exact
            (StandardPhysicalCharacterBridge.standardExponent_normalizeWeight
              e).symm
        · simp [physicalProjectKey, standardKeyEmbedding,
            affineProjectKey]
    _ = Finsupp.mapDomain standardKeyEmbedding
          (Finsupp.mapDomain
            (affineProjectKey (0 : ℤ →+ A) s.offset)
            s.rep.ambientLaurentModel.poly) :=
      Finsupp.mapDomain_comp

/-- At `(-2,3)`, the common physical resolved source is precisely the
injective image of the normalized standard charge-orbit bridge source. -/
theorem sourcePhysicalResolvedCharacter_standard
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A) :
    sourcePhysicalResolvedCharacter (-2) 3 source =
      embedStandardCharacter
        (FiniteChargedContinuousUnitarySource.resolvedCharacter
          source (0 : ℤ →+ A)) := by
  induction source with
  | nil =>
      rfl
  | cons s source ih =>
      change
        summandPhysicalResolvedCharacter (-2) 3 s +
            sourcePhysicalResolvedCharacter (-2) 3 source =
          embedStandardCharacter
            (s.toModeled.resolved (0 : ℤ →+ A) +
              FiniteChargedContinuousUnitarySource.resolvedCharacter
                source (0 : ℤ →+ A))
      rw [embedStandardCharacter_add,
        summandPhysicalResolvedCharacter_standard, ih]

theorem standardExponent_smReducedWeight (i : Fin 15) :
    StandardSMCharacterTarget.standardExponent
        (StandardSMCharacterTarget.smReducedWeight i) =
      PhysicalTorusCharacterBridge.smExponent i := by
  fin_cases i <;> ext j <;> fin_cases j <;> decide

theorem exactSMResolvedCharacter_standard
    {A : Type*} (generations : ℤ) (charges : Charges A) :
    PhysicalChargeResolvedBridge.exactSMResolvedCharacter
        generations charges =
      embedStandardCharacter
        (StandardSMCharacterTarget.exactSMResolvedCharacter
          generations charges) := by
  classical
  unfold PhysicalChargeResolvedBridge.exactSMResolvedCharacter
    StandardSMCharacterTarget.exactSMResolvedCharacter
    embedStandardCharacter
  rw [Finsupp.mapDomain_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finsupp.mapDomain_single]
  apply congrArg (fun key => Finsupp.single key generations)
  apply Prod.ext
  · exact (standardExponent_smReducedWeight i).symm
  · rfl

theorem singletResolvedCharacter_standard
    {A : Type*} (singlets : A →₀ ℤ) :
    PhysicalChargeResolvedBridge.singletResolvedCharacter singlets =
      embedStandardCharacter
        (StandardSMCharacterTarget.singletResolvedCharacter singlets) := by
  unfold PhysicalChargeResolvedBridge.singletResolvedCharacter
    StandardSMCharacterTarget.singletResolvedCharacter
    embedStandardCharacter
  calc
    Finsupp.mapDomain (fun q => ((0 : PhysicalExponent), q)) singlets =
        Finsupp.mapDomain
          (standardKeyEmbedding ∘
            fun q => ((0 : StandardAbelianCharge.ReducedWeight), q))
              singlets := by
      apply Finsupp.mapDomain_congr
      intro q _hq
      apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · rfl
    _ = Finsupp.mapDomain standardKeyEmbedding
          (Finsupp.mapDomain
            (fun q => ((0 : StandardAbelianCharge.ReducedWeight), q))
              singlets) :=
      Finsupp.mapDomain_comp

theorem exactSMWithSingletsResolvedCharacter_standard
    {A : Type*} (generations : ℤ) (charges : Charges A)
    (singlets : A →₀ ℤ) :
    PhysicalChargeResolvedBridge.exactSMWithSingletsResolvedCharacter
        generations charges singlets =
      embedStandardCharacter
        (StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter
          generations charges singlets) := by
  rw [PhysicalChargeResolvedBridge.exactSMWithSingletsResolvedCharacter,
    StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter,
    embedStandardCharacter_add, exactSMResolvedCharacter_standard,
    singletResolvedCharacter_standard]

/-!
## One spectrum premise supplies hypercharge character rigidity and standard charge-orbit bridge
-/

/-- Forgetting the residual charge in one exact resolved physical spectrum
produces the function-level hypercharge character rigidity spectrum of the actual source. -/
theorem characterOnPhysicalTorus_of_exactResolved
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ)
    (m n : ℤ)
    (hExact : sourcePhysicalResolvedCharacter m n source =
      exactSMWithSingletsResolvedCharacter
        generations charges singlets) :
    IsExactSMCharacterOnPhysicalTorus
      (chi := source.toVirtual) generations
      (totalSingletMultiplicity singlets) m n := by
  intro x
  rw [← (FiniteChargedContinuousUnitarySource.ambientLaurentModel
      source).evaluates_character,
    ← eval_restrictIntegralCharacter_eq_diagonalEval,
    ← forgetCharge_sourcePhysicalResolvedCharacter,
    hExact, forgetCharge_exactSMWithSingletsResolvedCharacter]

/-- hypercharge character rigidity therefore fixes an arbitrary integral physical cocharacter directly
from the single charge-resolved spectrum certificate. -/
theorem eq_standard_of_exactResolved
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ)
    (m n : ℤ) (hGenerations : generations ≠ 0)
    (hExact : sourcePhysicalResolvedCharacter m n source =
      exactSMWithSingletsResolvedCharacter
        generations charges singlets) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_continuousUnitarySource_characterOnPhysicalTorus
    source generations (totalSingletMultiplicity singlets) m n
      hGenerations
      (characterOnPhysicalTorus_of_exactResolved
        source generations charges singlets m n hExact)

/-- Once hypercharge character rigidity has selected the standard pair, injectivity of the standard key
embedding recovers the exact normalized standard charge-orbit bridge character. -/
theorem standardResolvedCharacter_eq_target_of_exactResolved
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ)
    (hExact : sourcePhysicalResolvedCharacter (-2) 3 source =
      exactSMWithSingletsResolvedCharacter
        generations charges singlets) :
    FiniteChargedContinuousUnitarySource.resolvedCharacter
        source (0 : ℤ →+ A) =
      StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter
        generations charges singlets := by
  apply embedStandardCharacter_injective
  exact (sourcePhysicalResolvedCharacter_standard source).symm.trans
    (hExact.trans
      (exactSMWithSingletsResolvedCharacter_standard
        generations charges singlets))

/-!
## Strict ordinary Abelian specialization
-/

theorem blockProjectKey_zero_zero
    {A : Type*} [AddCommGroup A]
    (x : RawResolvedKey A) :
    blockProjectKey (0 : A) 0 x = (normalizeWeight x.1, x.2) := by
  rcases x with ⟨e, q⟩
  simp [blockProjectKey, blockCharge]

theorem affineProjectKey_zero
    {A : Type*} [AddCommGroup A]
    (offset : A) (e : AmbientWeightLattice.Exponent) :
    affineProjectKey (0 : ℤ →+ A) offset e =
      (normalizeWeight e, offset) := by
  simp [affineProjectKey]

theorem blockResolved_zero_zero_rawResolvedSummand
    {A : Type*} [AddCommGroup A]
    (s : ChargedContinuousUnitarySummand A) :
    blockResolved (0 : A) 0 (rawResolvedSummand s) =
      s.toModeled.resolved (0 : ℤ →+ A) := by
  unfold blockResolved rawResolvedSummand rawResolvedWithOffset
    ChargedContinuousUnitarySummand.toModeled
    ChargedModeledVirtualSummand.resolved
    StandardPhysicalSource.chargeResolvedWithOffset
  rw [Finsupp.mapDomain_smul]
  congr 1
  calc
    Finsupp.mapDomain (blockProjectKey (0 : A) 0)
        (Finsupp.mapDomain (fun e => (e, s.offset))
          s.rep.ambientLaurentModel.poly) =
      Finsupp.mapDomain
          (blockProjectKey (0 : A) 0 ∘ fun e => (e, s.offset))
          s.rep.ambientLaurentModel.poly :=
      Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          (affineProjectKey (0 : ℤ →+ A) s.offset)
          s.rep.ambientLaurentModel.poly := by
      apply Finsupp.mapDomain_congr
      intro e _he
      simp only [Function.comp_apply]
      rw [blockProjectKey_zero_zero, affineProjectKey_zero]

/-- The zero block-gauge projection is the existing normalized charged-source
character with zero central shift. -/
theorem blockResolved_zero_zero_rawResolvedSource
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A) :
    blockResolved (0 : A) 0 (rawResolvedSource source) =
      FiniteChargedContinuousUnitarySource.resolvedCharacter
        source (0 : ℤ →+ A) := by
  induction source with
  | nil =>
      rfl
  | cons s source ih =>
      change
        blockResolved (0 : A) 0
            (rawResolvedSummand s + rawResolvedSource source) =
          s.toModeled.resolved (0 : ℤ →+ A) +
            FiniteChargedContinuousUnitarySource.resolvedCharacter
              source (0 : ℤ →+ A)
      rw [show blockResolved (0 : A) 0
            (rawResolvedSummand s + rawResolvedSource source) =
          blockResolved (0 : A) 0 (rawResolvedSummand s) +
            blockResolved (0 : A) 0 (rawResolvedSource source) from
        Finsupp.mapDomain_add,
        blockResolved_zero_zero_rawResolvedSummand, ih]

/-- The charged source obtained by decomposing each strict ordinary action
into its full character eigenspaces. -/
def ordinaryChargedSource
    {H : Type u} [CommGroup H]
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    FiniteChargedContinuousUnitarySource
      (FiniteAbelianChargeSectors.ChargeLabel H) :=
  source.toCommonGaugeSource.toChargedSource

/-- The full charge-sector source is only a refinement of the original
ordinary source: after charge labels are forgotten, their actual restricted
`SU(6)` characters agree pointwise. -/
theorem ordinaryChargedSource_restrictedCharacter_eq
    {H : Type u} [CommGroup H]
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (t : AmbientLaurent.DiagonalPoint) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        (ordinaryChargedSource source).toVirtual t =
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        source.toFiniteVirtual t := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        AmbientCharacterBridge.finiteVirtualRestrictedCharacter
            (StandardPhysicalSource.FiniteChargedContinuousUnitarySource.toVirtual
              (s.toCommonGaugeSummand.toChargedSource ++
                ordinaryChargedSource source)) t =
          (s.coeff : ℂ) * ActualRestriction.restrictedCharacter
              (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.rho
                (StandardBlockGaugeCancellation.OrdinaryAbelianSummand.rep s)) t +
            AmbientCharacterBridge.finiteVirtualRestrictedCharacter
              (StandardBlockGaugeCancellation.OrdinaryAbelianSource.toFiniteVirtual
                source) t
      rw [StandardPhysicalSource.FiniteChargedContinuousUnitarySource.finiteVirtualRestrictedCharacter_toVirtual_append,
        StandardBlockGaugeCancellation.CommonGaugeSummand.toChargedSource_restrictedCharacter_eq,
        ih]
      rfl

/-- Faithfulness of the common diagonal evaluator upgrades the preceding
trace identity to equality of the canonical normalized ambient Laurent
polynomials.  Thus the charge refinement used by standard charge-orbit bridge and the original hypercharge character rigidity
source are literally the same Laurent character after forgetting charges. -/
theorem ordinaryChargedSource_ambientLaurentModel_poly_eq
    {H : Type u} [CommGroup H]
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    (FiniteChargedContinuousUnitarySource.ambientLaurentModel
        (ordinaryChargedSource source)).poly =
      (StandardBlockGaugeCancellation.OrdinaryAbelianSource.ambientLaurentModel
        source).poly := by
  apply AmbientLaurent.diagonalEval_faithful
  intro t
  rw [(FiniteChargedContinuousUnitarySource.ambientLaurentModel
      (ordinaryChargedSource source)).evaluates_character,
    (StandardBlockGaugeCancellation.OrdinaryAbelianSource.ambientLaurentModel
      source).evaluates_character,
    ordinaryChargedSource_restrictedCharacter_eq]

/-- The existing standard charge-orbit bridge character for a strict ordinary action is exactly the
zero-shift normalized character of its charged-sector source. -/
theorem ordinaryAbelianResolvedCharacter_eq_chargedSource
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    ordinaryAbelianResolvedCharacter iota W source =
      FiniteChargedContinuousUnitarySource.resolvedCharacter
        (ordinaryChargedSource source)
        (0 : ℤ →+ FiniteAbelianChargeSectors.ChargeLabel H) := by
  unfold ordinaryAbelianResolvedCharacter actualBlockResolvedCharacter
  dsimp only
  rw [colorCharge_actualBlockGaugeHom_identity,
    weakCharge_actualBlockGaugeHom_identity]
  exact blockResolved_zero_zero_rawResolvedSource
    (ordinaryChargedSource source)

/-- The single physical normal form attached canonically to a strict
ordinary Abelian source. -/
def ordinaryPhysicalResolvedCharacter
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    PhysicalResolvedCharacter
      (FiniteAbelianChargeSectors.ChargeLabel H) :=
  sourcePhysicalResolvedCharacter m n (ordinaryChargedSource source)

/-- Forgetting the residual charge from the strict ordinary source gives the
physical restriction of the original source's canonical hypercharge character rigidity Laurent model,
not merely that of an auxiliary sector-expanded source. -/
theorem forgetCharge_ordinaryPhysicalResolvedCharacter
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    forgetCharge (ordinaryPhysicalResolvedCharacter m n source) =
      restrictIntegralCharacter m n
        (StandardBlockGaugeCancellation.OrdinaryAbelianSource.ambientLaurentModel
          source).poly := by
  unfold ordinaryPhysicalResolvedCharacter
  rw [forgetCharge_sourcePhysicalResolvedCharacter,
    ordinaryChargedSource_ambientLaurentModel_poly_eq]

/-- One exact charge-resolved physical spectrum is therefore a function-level
hypercharge character rigidity spectrum certificate for the original finite virtual `SU(6)` source. -/
theorem ordinaryCharacterOnPhysicalTorus_of_exactResolved
    {H : Type u} [CommGroup H]
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (generations : ℤ)
    (charges : Charges (FiniteAbelianChargeSectors.ChargeLabel H))
    (singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ)
    (m n : ℤ)
    (hExact : ordinaryPhysicalResolvedCharacter m n source =
      exactSMWithSingletsResolvedCharacter generations charges singlets) :
    IsExactSMCharacterOnPhysicalTorus
      (chi := source.toFiniteVirtual) generations
      (totalSingletMultiplicity singlets) m n := by
  intro x
  rw [← (StandardBlockGaugeCancellation.OrdinaryAbelianSource.ambientLaurentModel
      source).evaluates_character,
    ← eval_restrictIntegralCharacter_eq_diagonalEval,
    ← forgetCharge_ordinaryPhysicalResolvedCharacter,
    hExact, forgetCharge_exactSMWithSingletsResolvedCharacter]

/-- A single exact physical spectrum on a strict ordinary source fixes the
cocharacter by hypercharge character rigidity. -/
theorem ordinary_eq_standard_of_exactResolved
    {H : Type u} [CommGroup H]
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (generations : ℤ)
    (charges : Charges (FiniteAbelianChargeSectors.ChargeLabel H))
    (singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ)
    (m n : ℤ) (hGenerations : generations ≠ 0)
    (hExact : ordinaryPhysicalResolvedCharacter m n source =
      exactSMWithSingletsResolvedCharacter
        generations charges singlets) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_virtualModel_characterOnPhysicalTorus
    (StandardBlockGaugeCancellation.OrdinaryAbelianSource.ambientLaurentModel
      source)
    generations (totalSingletMultiplicity singlets) m n hGenerations
    (ordinaryCharacterOnPhysicalTorus_of_exactResolved
      source generations charges singlets m n hExact)

/-- The very same exact spectrum, after hypercharge character rigidity fixes the pair, supplies the local
coefficient certificate consumed by standard charge-orbit bridge. -/
theorem ordinaryCoefficientSpectrum_of_exactResolved
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (generations : ℤ)
    (charges : Charges (FiniteAbelianChargeSectors.ChargeLabel H))
    (singlets : FiniteAbelianChargeSectors.ChargeLabel H →₀ ℤ)
    (m n : ℤ) (hGenerations : generations ≠ 0)
    (hExact : ordinaryPhysicalResolvedCharacter m n source =
      exactSMWithSingletsResolvedCharacter
        generations charges singlets) :
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter iota W source)
      generations charges singlets := by
  obtain ⟨rfl, rfl⟩ := ordinary_eq_standard_of_exactResolved
    source generations charges singlets m n hGenerations hExact
  apply
    StandardPhysicalSpectrumBridge.IsExactSMOnlyCoefficientSpectrum.of_resolvedCharacter_eq
  rw [ordinaryAbelianResolvedCharacter_eq_chargedSource]
  exact standardResolvedCharacter_eq_target_of_exactResolved
    (ordinaryChargedSource source) generations charges singlets hExact

end

end PhysicalChargeResolvedBridge
end GUT
