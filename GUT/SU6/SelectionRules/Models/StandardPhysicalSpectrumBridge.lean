import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalCharacterBridge
import Mathlib.Tactic

open Physics

open Math

/-!
# Physical SM-only spectrum data for the standard branch

This file expresses the remaining low-energy chiral-spectrum input by local
coefficient conditions rather than by an unexplained equality of whole trace
characters.  The conditions say that the fifteen non-singlet Standard Model
weights have the stated generation multiplicity, the zero gauge weight has
the supplied finite singlet index, and every other nonzero gauge weight has
zero chiral index.

Lean proves that these conditions are equivalent to equality with the
canonical charge-resolved `Finsupp` target.  Combined with the actual source
trace calculation in `StandardPhysicalCharacterBridge`, they construct the
whole product-group character equivalence required by standard charge-orbit bridge.
-/

namespace GUT
namespace StandardPhysicalSpectrumBridge

noncomputable section

open FiniteAbelianChargeSectors
open PhysicalRestrictionBridge
open StandardAbelianCharge
open StandardBranchProtonObstruction
open StandardPhysicalCharacterBridge
open StandardSMCharacterTarget

universe u

abbrev ResidualCharge (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-!
## Exact coefficient-level spectrum
-/

theorem smReducedWeight_injective :
    Function.Injective smReducedWeight := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [smReducedWeight]

theorem smResolvedKey_injective
    {A : Type*} (k : Charges A) :
    Function.Injective (smResolvedKey k) := by
  intro i j hij
  apply smReducedWeight_injective
  exact congrArg Prod.fst hij

theorem smReducedWeight_ne_zero (i : Fin 15) :
    smReducedWeight i ≠ 0 := by
  fin_cases i <;> decide

theorem zeroWeightKey_injective {A : Type*} :
    Function.Injective (fun q : A => ((0 : ReducedWeight), q)) := by
  intro q r h
  exact congrArg Prod.snd h

@[simp]
theorem singletResolvedCharacter_apply_zero
    {A : Type*} (singlets : A →₀ Int) (q : A) :
    singletResolvedCharacter singlets ((0 : ReducedWeight), q) =
      singlets q := by
  exact Finsupp.mapDomain_apply_of_injective zeroWeightKey_injective singlets q

theorem exactSMResolvedCharacter_apply_smResolvedKey
    {A : Type*} (generations : Int) (k : Charges A) (i : Fin 15) :
    exactSMResolvedCharacter generations k (smResolvedKey k i) =
      generations := by
  classical
  simp [exactSMResolvedCharacter, Finsupp.single_apply,
    (smResolvedKey_injective k).eq_iff]

theorem exactSMResolvedCharacter_apply_of_notMem_range
    {A : Type*} (generations : Int) (k : Charges A)
    (key : ResolvedKey A) (hkey : key ∉ Set.range (smResolvedKey k)) :
    exactSMResolvedCharacter generations k key = 0 := by
  classical
  have hne : ∀ i : Fin 15, smResolvedKey k i ≠ key := by
    intro i hi
    exact hkey ⟨i, hi⟩
  simp [exactSMResolvedCharacter, hne]

/-- A coefficient-level formulation of an exact SM-only chiral index.

Vectorlike pairs may be present in the underlying matter spaces, but cancel
in `p`; the statement concerns the finite virtual chiral spectrum used by the
no-go theorem. -/
structure IsExactSMOnlyCoefficientSpectrum
    {A : Type*} (p : ResolvedCharacter A) (generations : Int)
    (k : Charges A) (singlets : A →₀ Int) : Prop where
  smMultiplicity : ∀ i : Fin 15,
    p (smResolvedKey k i) = generations
  singletMultiplicity : ∀ q : A,
    p ((0 : ReducedWeight), q) = singlets q
  noExoticNonSinglets : ∀ key : ResolvedKey A,
    key.1 ≠ 0 → key ∉ Set.range (smResolvedKey k) → p key = 0

namespace IsExactSMOnlyCoefficientSpectrum

variable {A : Type*} {p : ResolvedCharacter A} {generations : Int}
  {k : Charges A} {singlets : A →₀ Int}

/-- The local physical spectrum conditions determine the entire canonical
charge-resolved Laurent character. -/
theorem resolvedCharacter_eq
    (hSpectrum :
      IsExactSMOnlyCoefficientSpectrum p generations k singlets) :
    p = exactSMWithSingletsResolvedCharacter generations k singlets := by
  classical
  ext key
  rcases key with ⟨w, q⟩
  by_cases hw : w = 0
  · subst w
    have hNotSM :
        ((0 : ReducedWeight), q) ∉ Set.range (smResolvedKey k) := by
      rintro ⟨i, hi⟩
      exact smReducedWeight_ne_zero i (congrArg Prod.fst hi)
    rw [hSpectrum.singletMultiplicity]
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations k ((0 : ReducedWeight), q) hNotSM,
      singletResolvedCharacter_apply_zero]
    exact (zero_add _).symm
  · by_cases hSM : (w, q) ∈ Set.range (smResolvedKey k)
    · rcases hSM with ⟨i, hi⟩
      rw [← hi, hSpectrum.smMultiplicity]
      simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
      rw [exactSMResolvedCharacter_apply_smResolvedKey]
      change generations = generations +
        singletResolvedCharacter singlets
          (smReducedWeight i, smCharge k i)
      rw [singletResolvedCharacter_apply_of_weight_ne_zero
        singlets (smReducedWeight_ne_zero i)]
      exact (add_zero _).symm
    · rw [hSpectrum.noExoticNonSinglets (w, q) hw hSM]
      simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
      rw [exactSMResolvedCharacter_apply_of_notMem_range
        generations k (w, q) hSM,
        singletResolvedCharacter_apply_of_weight_ne_zero singlets hw]
      exact (zero_add _).symm

/-- Conversely, equality with the canonical target exposes exactly the local
SM multiplicities, arbitrary singlet index, and absence of chiral exotics. -/
theorem of_resolvedCharacter_eq
    (h : p = exactSMWithSingletsResolvedCharacter generations k singlets) :
    IsExactSMOnlyCoefficientSpectrum p generations k singlets := by
  classical
  rw [h]
  constructor
  · intro i
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_smResolvedKey]
    change generations +
      singletResolvedCharacter singlets
        (smReducedWeight i, smCharge k i) = generations
    rw [singletResolvedCharacter_apply_of_weight_ne_zero
      singlets (smReducedWeight_ne_zero i)]
    exact add_zero _
  · intro q
    have hNotSM :
        ((0 : ReducedWeight), q) ∉ Set.range (smResolvedKey k) := by
      rintro ⟨i, hi⟩
      exact smReducedWeight_ne_zero i (congrArg Prod.fst hi)
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations k ((0 : ReducedWeight), q) hNotSM,
      singletResolvedCharacter_apply_zero]
    exact zero_add _
  · intro key hWeight hNotSM
    simp only [exactSMWithSingletsResolvedCharacter, Finsupp.add_apply]
    rw [exactSMResolvedCharacter_apply_of_notMem_range
      generations k key hNotSM,
      singletResolvedCharacter_apply_of_weight_ne_zero singlets hWeight]
    exact zero_add 0

theorem iff_resolvedCharacter_eq :
    IsExactSMOnlyCoefficientSpectrum p generations k singlets ↔
      p = exactSMWithSingletsResolvedCharacter generations k singlets :=
  ⟨resolvedCharacter_eq, of_resolvedCharacter_eq⟩

end IsExactSMOnlyCoefficientSpectrum

/-!
## From physical coefficients to actual character equivalence
-/

/-- The coefficient-level SM-only spectrum supplies the whole actual
product-group character equivalence. -/
theorem sourceProductRepresentation_characterEquivalent_of_spectrum
    {H : Type u} [CommGroup H]
    (centralCharacter : H →* Circle)
    (matter : StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ResidualCharge H))
    (generations : Int) (k : Charges (ResidualCharge H))
    (singlets : ResidualCharge H →₀ Int)
    (hSpectrum : IsExactSMOnlyCoefficientSpectrum
      (matter.resolvedCharacter (centralDegreeCharge centralCharacter))
      generations k singlets) :
    IsSMTargetCharacterEquivalent
      (sourceProductRepresentation centralCharacter matter)
      generations k singlets := by
  intro g
  rcases g with ⟨x, h⟩
  calc
    FiniteVirtualGroupRepresentation.character
        (sourceProductRepresentation centralCharacter matter) (x, h) =
        eval
          (matter.resolvedCharacter
            (centralDegreeCharge centralCharacter)) x.toAdd h := by
      simpa using sourceProductRepresentation_character
        centralCharacter matter x.toAdd h
    _ = eval
          (exactSMWithSingletsResolvedCharacter generations k singlets)
          x.toAdd h := by
      rw [hSpectrum.resolvedCharacter_eq]
    _ = FiniteVirtualGroupRepresentation.character
          (targetWithSinglets generations k singlets) (x, h) := by
      simpa using
        (targetWithSinglets_character generations k singlets x.toAdd h).symm

/-- A standard gauge-factorized physical source whose low-energy chiral
spectrum is stated coefficient by coefficient.  No source character model or
whole-character equivalence is a field. -/
structure PureSMPhysicalSpectrumSource
    (H : Type u) [CommGroup H] where
  centralCharacter : H →* Circle
  matter : FiniteResidualActionFactorization.StandardCentralSource
    H centralCharacter
  generations : Int
  generations_ne : generations ≠ 0
  charges : Charges (ResidualCharge H)
  singlets : ResidualCharge H →₀ Int
  spectrum : IsExactSMOnlyCoefficientSpectrum
    (matter.toChargedSource.resolvedCharacter
      (centralDegreeCharge centralCharacter))
    generations charges singlets

namespace PureSMPhysicalSpectrumSource

variable {H : Type u} [CommGroup H]

def toPhysicalCharacterSource (S : PureSMPhysicalSpectrumSource H) :
    PureSMStandardPhysicalCharacterSource H where
  centralCharacter := S.centralCharacter
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent :=
    sourceProductRepresentation_characterEquivalent_of_spectrum
      S.centralCharacter S.matter.toChargedSource S.generations S.charges
      S.singlets S.spectrum

theorem resolvedCharacter_eq_target (S : PureSMPhysicalSpectrumSource H) :
    S.matter.toChargedSource.resolvedCharacter
        (centralDegreeCharge S.centralCharacter) =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  S.spectrum.resolvedCharacter_eq

theorem charge_equalities (S : PureSMPhysicalSpectrumSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toPhysicalCharacterSource.charge_equalities

/-- Main standard-branch conclusion from the explicit coefficient-level
SM-only spectrum.  This is standard charge-orbit bridge followed by Abelian proton-operator neutrality and has no anomaly premise. -/
theorem protonCharacters_eq_one (S : PureSMPhysicalSpectrumSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toPhysicalCharacterSource.protonCharacters_eq_one

theorem protonPhases_eq_one (S : PureSMPhysicalSpectrumSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  S.toPhysicalCharacterSource.protonPhases_eq_one h

end PureSMPhysicalSpectrumSource

/-- Continuous ordinary-Abelian specialization of the coefficient-level
physical source. -/
structure PureSMContinuousPhysicalSpectrumSource
    (H : Type u) [CommGroup H] [TopologicalSpace H] where
  centralCharacter : H →ₜ* Circle
  matter : FiniteResidualActionFactorization.ContinuousStandardCentralSource
    H centralCharacter
  generations : Int
  generations_ne : generations ≠ 0
  charges : Charges (ResidualCharge H)
  singlets : ResidualCharge H →₀ Int
  spectrum : IsExactSMOnlyCoefficientSpectrum
    (matter.toChargedSource.resolvedCharacter
      (centralDegreeCharge (centralCharacter : H →* Circle)))
    generations charges singlets

namespace PureSMContinuousPhysicalSpectrumSource

variable {H : Type u} [CommGroup H] [TopologicalSpace H]

def toPhysicalSpectrumSource
    (S : PureSMContinuousPhysicalSpectrumSource H) :
    PureSMPhysicalSpectrumSource H where
  centralCharacter := (S.centralCharacter : H →* Circle)
  matter := S.matter.toStandardCentralSource
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  spectrum := S.spectrum

theorem charge_equalities
    (S : PureSMContinuousPhysicalSpectrumSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toPhysicalSpectrumSource.charge_equalities

theorem protonCharacters_eq_one
    (S : PureSMContinuousPhysicalSpectrumSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toPhysicalSpectrumSource.protonCharacters_eq_one

end PureSMContinuousPhysicalSpectrumSource

/-- Explicit finite-Abelian specialization. -/
abbrev PureSMFinitePhysicalSpectrumSource
    (H : Type u) [CommGroup H] [Finite H] :=
  PureSMPhysicalSpectrumSource H

namespace PureSMFinitePhysicalSpectrumSource

variable {H : Type u} [CommGroup H] [Finite H]

theorem charge_equalities (S : PureSMFinitePhysicalSpectrumSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  PureSMPhysicalSpectrumSource.charge_equalities S

theorem protonCharacters_eq_one
    (S : PureSMFinitePhysicalSpectrumSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  PureSMPhysicalSpectrumSource.protonCharacters_eq_one S

theorem protonPhases_eq_one
    (S : PureSMFinitePhysicalSpectrumSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  PureSMPhysicalSpectrumSource.protonPhases_eq_one S h

end PureSMFinitePhysicalSpectrumSource

end
end StandardPhysicalSpectrumBridge
end GUT
