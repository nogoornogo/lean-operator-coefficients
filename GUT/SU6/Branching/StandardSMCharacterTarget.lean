import Physics.StandardModel.Spectrum.Representations.FiniteSMTarget
import GUT.SU6.Branching.PhysicalSMTorusTarget
import GUT.SU6.SelectionRules.StandardBranch.FiniteResidualActionFactorization
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

open Physics

open Math

/-!
# The charge-resolved Standard Model character target

The standard charge-orbit bridge source character is a finite `Finsupp` on a normalized `SU(5)` weight
and an Abelian residual charge.  This file evaluates that object on the
product of the physical compact four-torus and the residual group itself.
Dedekind linear independence proves that the evaluator is faithful for every
Abelian group, including finite groups.

The fifteen Standard Model weights with independently specified charges for
`Q`, `u^c`, `d^c`, `L`, and `e^c`, together with arbitrary charge-resolved
gauge singlets, are then realized as an actual finite virtual sum of
one-dimensional representations of that product group.  Character
equivalence with this target recovers the exact charge profiles required by
the anomaly-independent `standard charge-orbit bridge -> Abelian proton-operator neutrality` route.
-/

open scoped BigOperators

namespace GUT
namespace StandardSMCharacterTarget
open Physics.StandardSMCharacterTarget

noncomputable section

open StandardAbelianCharge
open StandardBranchProtonObstruction
open PhysicalRestrictionBridge

universe u

abbrev CompactTorus := Multiplicative (UnitAddTorus (Fin 4))
abbrev CombinedGroup (H : Type u) := CompactTorus × H
abbrev ChargeLabel (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-!
## Faithful joint character evaluation
-/

/-- Coercion of a circle-valued character to a complex-valued character. -/
def circleCoeMonoidHom : Circle →* ℂ where
  toFun z := (z : ℂ)
  map_one' := rfl
  map_mul' _ _ := rfl

def chargeMonoidHom
    {H : Type u} [CommGroup H] (q : ChargeLabel H) : H →* ℂ :=
  circleCoeMonoidHom.comp q.toMul

/-- Express a normalized `SU(5)` weight in the physical torus coordinates at
the standard cocharacter pair `(-2,3)`. -/
def standardExponent (w : ReducedWeight) : Fin 4 → ℤ :=
  ![w 0 - w 2,
    w 1 - w 2,
    w 3,
    -2 * (w 0 + w 1 + w 2) + 3 * w 3]

@[simp]
theorem standardExponent_zero (w : ReducedWeight) :
    standardExponent w 0 = w 0 - w 2 := rfl

@[simp]
theorem standardExponent_one (w : ReducedWeight) :
    standardExponent w 1 = w 1 - w 2 := rfl

@[simp]
theorem standardExponent_two (w : ReducedWeight) :
    standardExponent w 2 = w 3 := rfl

@[simp]
theorem standardExponent_three (w : ReducedWeight) :
    standardExponent w 3 =
      -2 * (w 0 + w 1 + w 2) + 3 * w 3 := rfl

theorem standardExponent_injective : Function.Injective standardExponent := by
  intro w v h
  have h0 : w 0 - w 2 = v 0 - v 2 := by
    simpa using congrFun h (0 : Fin 4)
  have h1 : w 1 - w 2 = v 1 - v 2 := by
    simpa using congrFun h (1 : Fin 4)
  have h2 : w 3 = v 3 := by
    simpa using congrFun h (2 : Fin 4)
  have h3 : -2 * (w 0 + w 1 + w 2) + 3 * w 3 =
      -2 * (v 0 + v 1 + v 2) + 3 * v 3 := by
    simpa using congrFun h (3 : Fin 4)
  have hw2 : w 2 = v 2 := by omega
  have hw0 : w 0 = v 0 := by omega
  have hw1 : w 1 = v 1 := by omega
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact h2

/-- The product character associated with a normalized `SU(5)` weight and a
residual-group character. -/
def keyMonoidHom
    {H : Type u} [CommGroup H]
    (key : ResolvedKey (ChargeLabel H)) : CombinedGroup H →* ℂ :=
  (PhysicalTorusCharacterBridge.Fourier.exponentMonoidHom
      (standardExponent key.1)).coprod
    (chargeMonoidHom key.2)

@[simp]
theorem keyMonoidHom_apply
    {H : Type u} [CommGroup H]
    (key : ResolvedKey (ChargeLabel H)) (x : CompactTorus) (h : H) :
    keyMonoidHom key (x, h) =
      UnitAddTorus.mFourier (standardExponent key.1) x.toAdd *
        ((key.2.toMul h : Circle) : ℂ) :=
  rfl

theorem keyMonoidHom_injective
    {H : Type u} [CommGroup H] :
    Function.Injective
      (keyMonoidHom (H := H) :
        ResolvedKey (ChargeLabel H) → CombinedGroup H →* ℂ) := by
  rintro ⟨e, q⟩ ⟨f, r⟩ h
  apply Prod.ext
  · apply standardExponent_injective
    apply PhysicalTorusCharacterBridge.Fourier.exponentMonoidHom_injective
    apply MonoidHom.ext
    intro x
    have hx := congrArg
      (fun phi : CombinedGroup H →* ℂ => phi (x, 1)) h
    simpa [keyMonoidHom, chargeMonoidHom, circleCoeMonoidHom] using hx
  · apply Additive.toMul.injective
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    have ha := congrArg
      (fun phi : CombinedGroup H →* ℂ => phi (1, a)) h
    change circleCoeMonoidHom (q.toMul a) =
      circleCoeMonoidHom (r.toMul a)
    simpa [keyMonoidHom, chargeMonoidHom] using ha

theorem linearIndependent_keyMonoidHom
    {H : Type u} [CommGroup H] :
    LinearIndependent ℂ
      (fun key : ResolvedKey (ChargeLabel H) =>
        (keyMonoidHom key : CombinedGroup H → ℂ)) := by
  exact (linearIndependent_monoidHom (CombinedGroup H) ℂ).comp
    keyMonoidHom keyMonoidHom_injective

/-- Evaluate a charge-resolved character on the physical compact torus and
the residual group. -/
def eval
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) : ℂ :=
  p.sum fun key c =>
    (c : ℂ) * keyMonoidHom key (Multiplicative.ofAdd x, h)

def toComplex
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    ResolvedKey (ChargeLabel H) →₀ ℂ :=
  Finsupp.mapRange (fun c : ℤ => (c : ℂ)) (by simp) p

@[simp]
theorem toComplex_apply
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H))
    (key : ResolvedKey (ChargeLabel H)) :
    toComplex p key = (p key : ℂ) := by
  simp [toComplex]

theorem eval_eq_linearCombination
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    Finsupp.linearCombination ℂ
        (fun key : ResolvedKey (ChargeLabel H) =>
          (keyMonoidHom key : CombinedGroup H → ℂ))
        (toComplex p) =
      fun g => eval p g.1.toAdd g.2 := by
  ext g
  rw [Finsupp.linearCombination_apply, toComplex,
    Finsupp.sum_mapRange_index]
  · simp only [eval, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro key _hkey
    rfl
  · intro key
    simp

theorem eval_faithful
    {H : Type u} [CommGroup H]
    (p q : ResolvedCharacter (ChargeLabel H))
    (h : ∀ (x : UnitAddTorus (Fin 4)) (a : H),
      eval p x a = eval q x a) :
    p = q := by
  have hlin :
      Finsupp.linearCombination ℂ
          (fun key : ResolvedKey (ChargeLabel H) =>
            (keyMonoidHom key : CombinedGroup H → ℂ))
          (toComplex p) =
        Finsupp.linearCombination ℂ
          (fun key : ResolvedKey (ChargeLabel H) =>
            (keyMonoidHom key : CombinedGroup H → ℂ))
          (toComplex q) := by
    rw [eval_eq_linearCombination p, eval_eq_linearCombination q]
    funext g
    exact h g.1.toAdd g.2
  have hComplex : toComplex p = toComplex q :=
    linearIndependent_keyMonoidHom.finsuppLinearCombination_injective hlin
  ext key
  exact Int.cast_injective (α := ℂ) (by
    simpa using congrArg
      (fun r : ResolvedKey (ChargeLabel H) →₀ ℂ => r key) hComplex)

/-!
## The fifteen charge-resolved Standard Model weights
-/


@[simp]
theorem rawReducedWeight_zero (w : ReducedWeight) :
    rawReducedWeight w (0 : Fin 5) = w 0 := by
  simpa using rawReducedWeight_castSucc w (0 : Fin 4)

@[simp]
theorem rawReducedWeight_one (w : ReducedWeight) :
    rawReducedWeight w (1 : Fin 5) = w 1 := by
  simpa using rawReducedWeight_castSucc w (1 : Fin 4)

@[simp]
theorem rawReducedWeight_two (w : ReducedWeight) :
    rawReducedWeight w (2 : Fin 5) = w 2 := by
  simpa using rawReducedWeight_castSucc w (2 : Fin 4)

@[simp]
theorem rawReducedWeight_three (w : ReducedWeight) :
    rawReducedWeight w (3 : Fin 5) = w 3 := by
  simpa using rawReducedWeight_castSucc w (3 : Fin 4)

@[simp]
theorem rawReducedWeight_four (w : ReducedWeight) :
    rawReducedWeight w (4 : Fin 5) = 0 := by
  simpa using rawReducedWeight_last w

theorem standardExponent_eq_restrictExponent_rawReducedWeight
    (w : ReducedWeight) :
    standardExponent w =
      PhysicalTorusCharacterBridge.restrictExponent (-2) 3
        (rawReducedWeight w) := by
  ext i
  fin_cases i <;>
    simp [standardExponent,
      PhysicalTorusCharacterBridge.restrictExponent]

/-- On the standard hypercharge torus, the normalized `SU(5)` weights above
are exactly the physical weights used by the hypercharge character rigidity target. -/
theorem restrictExponent_smReducedWeight (i : Fin 15) :
    PhysicalTorusCharacterBridge.restrictExponent (-2) 3
        (rawReducedWeight (smReducedWeight i)) =
      PhysicalTorusCharacterBridge.smExponent i := by
  rw [← standardExponent_eq_restrictExponent_rawReducedWeight]
  fin_cases i <;> ext j <;> fin_cases j <;> decide


/-!
## Actual one-dimensional target representations
-/

def weightRho
    {H : Type u} [CommGroup H]
    (key : ResolvedKey (ChargeLabel H)) :
    Representation ℂ (CombinedGroup H) ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (keyMonoidHom key g)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

theorem weightRho_character
    {H : Type u} [CommGroup H]
    (key : ResolvedKey (ChargeLabel H)) (g : CombinedGroup H) :
    (weightRho key).character g = keyMonoidHom key g := by
  change LinearMap.trace ℂ ℂ
    (LinearMap.lsmul ℂ ℂ (keyMonoidHom key g)) = _
  rw [show LinearMap.lsmul ℂ ℂ (keyMonoidHom key g) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (keyMonoidHom key g) by
    apply LinearMap.ext
    intro z
    simp [mul_comm]]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) _

def weightRepresentation
    {H : Type u} [CommGroup H]
    (key : ResolvedKey (ChargeLabel H)) :
    ActualGroupRepresentation (CombinedGroup H) where
  V := ℂ
  rho := weightRho key

def ofCharacter
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    FiniteVirtualGroupRepresentation (CombinedGroup H) :=
  p.support.toList.map fun key =>
    { coeff := p key
      rep := weightRepresentation key }

theorem character_ofCharacter
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character (ofCharacter p)
        (Multiplicative.ofAdd x, h) = eval p x h := by
  classical
  let summand : ResolvedKey (ChargeLabel H) →
      VirtualGroupSummand (CombinedGroup H) := fun key =>
    { coeff := p key
      rep := weightRepresentation key }
  have hList (l : List (ResolvedKey (ChargeLabel H))) :
      FiniteVirtualGroupRepresentation.character (l.map summand)
          (Multiplicative.ofAdd x, h) =
        (l.map fun key =>
          (p key : ℂ) * keyMonoidHom key
            (Multiplicative.ofAdd x, h)).sum := by
    induction l with
    | nil => rfl
    | cons key keys ih =>
        simp only [List.map_cons,
          FiniteVirtualGroupRepresentation.character,
          VirtualGroupSummand.character, List.sum_cons, ih]
        change
          (p key : ℂ) * (weightRho key).character
              (Multiplicative.ofAdd x, h) + _ = _
        rw [weightRho_character]
  rw [show ofCharacter p = p.support.toList.map summand by rfl, hList]
  simp [eval, Finsupp.sum]

def target
    {H : Type u} [CommGroup H]
    (generations : ℤ) (k : Charges (ChargeLabel H)) :
    FiniteVirtualGroupRepresentation (CombinedGroup H) :=
  ofCharacter (exactSMResolvedCharacter generations k)

theorem target_character
    {H : Type u} [CommGroup H]
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character (target generations k)
        (Multiplicative.ofAdd x, h) =
      eval (exactSMResolvedCharacter generations k) x h :=
  character_ofCharacter _ x h

def targetWithSinglets
    {H : Type u} [CommGroup H]
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ) :
    FiniteVirtualGroupRepresentation (CombinedGroup H) :=
  ofCharacter
    (exactSMWithSingletsResolvedCharacter generations k singlets)

theorem targetWithSinglets_character
    {H : Type u} [CommGroup H]
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (targetWithSinglets generations k singlets)
        (Multiplicative.ofAdd x, h) =
      eval (exactSMWithSingletsResolvedCharacter generations k singlets) x h :=
  character_ofCharacter _ x h

/-!
## From actual character equivalence to the standard charge-orbit bridge spectrum certificate
-/

/-- An actual finite virtual representation whose whole product-group
character is represented by the charge-resolved `Finsupp` `p`. -/
def IsCharacterModel
    {H : Type u} [CommGroup H]
    (source : FiniteVirtualGroupRepresentation (CombinedGroup H))
    (p : ResolvedCharacter (ChargeLabel H)) : Prop :=
  ∀ (x : UnitAddTorus (Fin 4)) (h : H),
    FiniteVirtualGroupRepresentation.character source
        (Multiplicative.ofAdd x, h) = eval p x h

theorem ofCharacter_isCharacterModel
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H)) :
    IsCharacterModel (ofCharacter p) p :=
  character_ofCharacter p

/-- Equality with the actual fifteen-weight target, together with arbitrary
gauge singlets, on the whole product group. -/
def IsSMTargetCharacterEquivalent
    {H : Type u} [CommGroup H]
    (source : FiniteVirtualGroupRepresentation (CombinedGroup H))
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ) : Prop :=
  FiniteVirtualGroupRepresentation.CharacterEquivalent
    source (targetWithSinglets generations k singlets)

theorem exactResolvedCharacter_of_characterEquivalent
    {H : Type u} [CommGroup H]
    {source : FiniteVirtualGroupRepresentation (CombinedGroup H)}
    {p : ResolvedCharacter (ChargeLabel H)}
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ)
    (hModel : IsCharacterModel source p)
    (hEquivalent :
      IsSMTargetCharacterEquivalent source generations k singlets) :
    p = exactSMWithSingletsResolvedCharacter generations k singlets := by
  apply eval_faithful
  intro x h
  calc
    eval p x h =
        FiniteVirtualGroupRepresentation.character source
          (Multiplicative.ofAdd x, h) := (hModel x h).symm
    _ = FiniteVirtualGroupRepresentation.character
          (targetWithSinglets generations k singlets)
          (Multiplicative.ofAdd x, h) :=
      hEquivalent (Multiplicative.ofAdd x, h)
    _ = eval
          (exactSMWithSingletsResolvedCharacter generations k singlets) x h :=
      targetWithSinglets_character generations k singlets x h

theorem ofCharacter_characterEquivalent_target_iff
    {H : Type u} [CommGroup H]
    (p : ResolvedCharacter (ChargeLabel H))
    (generations : ℤ) (k : Charges (ChargeLabel H)) :
    ∀ singlets : ChargeLabel H →₀ ℤ,
      FiniteVirtualGroupRepresentation.CharacterEquivalent
          (ofCharacter p) (targetWithSinglets generations k singlets) ↔
        p = exactSMWithSingletsResolvedCharacter generations k singlets := by
  intro singlets
  constructor
  · intro h
    exact exactResolvedCharacter_of_characterEquivalent generations k singlets
      (ofCharacter_isCharacterModel p) h
  · intro h
    subst p
    intro g
    rfl

theorem pureSMChargeSpectrum_of_characterEquivalent
    {H : Type u} [CommGroup H]
    {source : FiniteVirtualGroupRepresentation (CombinedGroup H)}
    {p : ResolvedCharacter (ChargeLabel H)}
    (generations : ℤ) (k : Charges (ChargeLabel H))
    (singlets : ChargeLabel H →₀ ℤ)
    (hModel : IsCharacterModel source p)
    (hEquivalent :
      IsSMTargetCharacterEquivalent source generations k singlets) :
    IsPureSMChargeSpectrum p generations k := by
  rw [exactResolvedCharacter_of_characterEquivalent
    generations k singlets hModel hEquivalent]
  exact exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum
    generations k singlets

/-- A continuous-unitary ultraviolet matter source together with an actual
product-group character realization and equality to the explicit Standard
Model target.  This replaces a primitive `IsPureSMChargeSpectrum` field by a
representation-theoretic character-equivalence hypothesis. -/
structure PureSMCharacterSource
    (H : Type u) [CommGroup H] where
  matter : StandardPhysicalSource.FiniteChargedContinuousUnitarySource
    (ChargeLabel H)
  centralCharge : ℤ →+ ChargeLabel H
  combinedRepresentation :
    FiniteVirtualGroupRepresentation (CombinedGroup H)
  characterModel : IsCharacterModel combinedRepresentation
    (matter.resolvedCharacter centralCharge)
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  characterEquivalent : IsSMTargetCharacterEquivalent
    combinedRepresentation generations charges singlets

namespace PureSMCharacterSource

variable {H : Type u} [CommGroup H]

def toPureSMChargedSource (S : PureSMCharacterSource H) :
    StandardPhysicalSource.PureSMChargedSource (ChargeLabel H) where
  matter := S.matter
  centralCharge := S.centralCharge
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  spectrum := pureSMChargeSpectrum_of_characterEquivalent
    S.generations S.charges S.singlets S.characterModel S.characterEquivalent

/-- The actual character source forces
`k_Q = k_u = k_e` and `k_d = k_L`. -/
theorem charge_equalities (S : PureSMCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton := by
  exact StandardAbelianCharge.su5OrbitCompatible_of_pureSM
    (S.matter.resolvedCharacter S.centralCharge)
    (S.matter.resolvedCharacter_isWeylInvariant S.centralCharge)
    S.generations S.generations_ne S.charges
    S.toPureSMChargedSource.spectrum

/-- Main standard charge-orbit bridge-to-Abelian proton-operator neutrality result from actual product-group character equivalence.
No anomaly equation is used. -/
theorem protonCharacters_eq_one (S : PureSMCharacterSource H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges = 1 :=
  FiniteAbelianChargeSectors.residual_protonCharacters_eq_one
    S.toPureSMChargedSource

theorem protonPhases_eq_one (S : PureSMCharacterSource H) (h : H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges h = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges h = 1 :=
  FiniteAbelianChargeSectors.residual_protonPhases_eq_one
    S.toPureSMChargedSource h

end PureSMCharacterSource

/-!
## Specialization to the gauge-factorized standard source
-/

/-- The standard-central gauge-action certificate together with an exact
whole-character statement for the resulting charge-resolved spectrum. -/
structure PureSMStandardCentralCharacterSource
    (H : Type u) [CommGroup H] where
  centralCharacter : H →* Circle
  matter :
    FiniteResidualActionFactorization.StandardCentralSource
      H centralCharacter
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  characterEquivalent :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (ofCharacter
        (matter.toChargedSource.resolvedCharacter
          (FiniteAbelianChargeSectors.centralDegreeCharge
            centralCharacter)))
      (targetWithSinglets generations charges singlets)

namespace PureSMStandardCentralCharacterSource

variable {H : Type u} [CommGroup H]

def toPureSMCharacterSource
    (S : PureSMStandardCentralCharacterSource H) :
    PureSMCharacterSource H where
  matter := S.matter.toChargedSource
  centralCharge :=
    FiniteAbelianChargeSectors.centralDegreeCharge S.centralCharacter
  combinedRepresentation := ofCharacter
    (S.matter.toChargedSource.resolvedCharacter
      (FiniteAbelianChargeSectors.centralDegreeCharge S.centralCharacter))
  characterModel := ofCharacter_isCharacterModel _
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent := S.characterEquivalent

theorem charge_equalities
    (S : PureSMStandardCentralCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toPureSMCharacterSource.charge_equalities

theorem protonCharacters_eq_one
    (S : PureSMStandardCentralCharacterSource H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges = 1 :=
  S.toPureSMCharacterSource.protonCharacters_eq_one

theorem protonPhases_eq_one
    (S : PureSMStandardCentralCharacterSource H) (h : H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges h = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges h = 1 :=
  S.toPureSMCharacterSource.protonPhases_eq_one h

end PureSMStandardCentralCharacterSource

/-- Explicit finite-Abelian specialization of the actual-character standard charge-orbit bridge
source. -/
abbrev PureSMFiniteCharacterSource
    (H : Type u) [CommGroup H] [Finite H] :=
  PureSMCharacterSource H

namespace PureSMFiniteCharacterSource

variable {H : Type u} [CommGroup H] [Finite H]

theorem charge_equalities (S : PureSMFiniteCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  PureSMCharacterSource.charge_equalities S

theorem protonCharacters_eq_one (S : PureSMFiniteCharacterSource H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges = 1 :=
  PureSMCharacterSource.protonCharacters_eq_one S

theorem protonPhases_eq_one
    (S : PureSMFiniteCharacterSource H) (h : H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges h = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges h = 1 :=
  PureSMCharacterSource.protonPhases_eq_one S h

end PureSMFiniteCharacterSource

/-- Finite-Abelian specialization retaining the complete standard-central
gauge-action factorization certificate. -/
abbrev PureSMFiniteStandardCentralCharacterSource
    (H : Type u) [CommGroup H] [Finite H] :=
  PureSMStandardCentralCharacterSource H

namespace PureSMFiniteStandardCentralCharacterSource

variable {H : Type u} [CommGroup H] [Finite H]

theorem charge_equalities
    (S : PureSMFiniteStandardCentralCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  PureSMStandardCentralCharacterSource.charge_equalities S

theorem protonCharacters_eq_one
    (S : PureSMFiniteStandardCentralCharacterSource H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges = 1 :=
  PureSMStandardCentralCharacterSource.protonCharacters_eq_one S

theorem protonPhases_eq_one
    (S : PureSMFiniteStandardCentralCharacterSource H) (h : H) :
    FiniteAbelianChargeSectors.protonFirstCharacter S.charges h = 1 ∧
      FiniteAbelianChargeSectors.protonSecondCharacter S.charges h = 1 :=
  PureSMStandardCentralCharacterSource.protonPhases_eq_one S h

end PureSMFiniteStandardCentralCharacterSource

end
end StandardSMCharacterTarget
end GUT
