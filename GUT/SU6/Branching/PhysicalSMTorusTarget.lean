import GUT.SU6.Characters.PhysicalTorusCharacterBridge
import GUT.SU6.SelectionRules.FlippedBranch.PhysicalRestrictionBridge
import GUT.SU6.Characters.AmbientTorus
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

open Math

/-!
# The actual Standard Model target on the physical compact torus

Every integral physical weight defines a one-dimensional representation of
the multiplicative form of `Circle^4`.  This file realizes an arbitrary finite
weight `Finsupp`, and in particular the exact Standard Model plus singlets
target, as an actual finite virtual representation whose trace character is
the faithful Fourier evaluator.
-/

namespace GUT
namespace PhysicalSMTorusTarget

noncomputable section

open PhysicalTorusCharacterBridge
open PhysicalRestrictionBridge

abbrev Group := Multiplicative (UnitAddTorus (Fin 4))

/-- The one-dimensional representation with integral physical weight `e`. -/
def weightRho (e : PhysicalExponent) : Representation ℂ Group ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (Fourier.exponentMonoidHom e g)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

theorem weightRho_character (e : PhysicalExponent) (g : Group) :
    (weightRho e).character g = Fourier.exponentMonoidHom e g := by
  change LinearMap.trace ℂ ℂ
    (LinearMap.lsmul ℂ ℂ (Fourier.exponentMonoidHom e g)) = _
  rw [show LinearMap.lsmul ℂ ℂ (Fourier.exponentMonoidHom e g) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
        (Fourier.exponentMonoidHom e g) by
    apply LinearMap.ext
    intro z
    simp [mul_comm]]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) _

def weightRepresentation (e : PhysicalExponent) :
    ActualGroupRepresentation Group where
  V := ℂ
  rho := weightRho e

/-- Realize a finite integral weight character by listing its nonzero
one-dimensional virtual summands. -/
def ofCharacter (p : IntegralPhysicalCharacter) :
    FiniteVirtualGroupRepresentation Group :=
  p.support.toList.map fun e =>
    { coeff := p e
      rep := weightRepresentation e }

theorem character_ofCharacter
    (p : IntegralPhysicalCharacter) (x : UnitAddTorus (Fin 4)) :
    FiniteVirtualGroupRepresentation.character (ofCharacter p)
        (Multiplicative.ofAdd x) =
      PhysicalTorusCharacterBridge.eval p x := by
  classical
  let summand : PhysicalExponent → VirtualGroupSummand Group := fun e =>
    { coeff := p e
      rep := weightRepresentation e }
  have hList (l : List PhysicalExponent) :
      FiniteVirtualGroupRepresentation.character (l.map summand)
          (Multiplicative.ofAdd x) =
        (l.map fun e =>
          (p e : ℂ) * UnitAddTorus.mFourier e x).sum := by
    induction l with
    | nil => rfl
    | cons e es ih =>
        simp only [List.map_cons,
          FiniteVirtualGroupRepresentation.character,
          VirtualGroupSummand.character, List.sum_cons, ih]
        change
          (p e : ℂ) * (weightRho e).character (Multiplicative.ofAdd x) + _ = _
        rw [weightRho_character]
        rfl
  rw [show ofCharacter p = p.support.toList.map summand by rfl,
    hList]
  simp [PhysicalTorusCharacterBridge.eval, Finsupp.sum]

/-- The actual finite virtual target for `generations` Standard Model
generations and an arbitrary net gauge-singlet index. -/
def target (generations singlets : ℤ) :
    FiniteVirtualGroupRepresentation Group :=
  ofCharacter (exactSMCharacter generations singlets)

theorem target_character
    (generations singlets : ℤ) (x : UnitAddTorus (Fin 4)) :
    FiniteVirtualGroupRepresentation.character (target generations singlets)
        (Multiplicative.ofAdd x) =
      PhysicalTorusCharacterBridge.eval
        (exactSMCharacter generations singlets) x :=
  character_ofCharacter _ x

/-!
## The physical torus homomorphism into SU(6)
-/

/-- Convert the additive physical torus map to the five multiplicative circle
coordinates of the ambient maximal torus. -/
theorem ambientTorusPoint_zero (m n : ℤ) :
    ambientTorusPoint m n (0 : UnitAddTorus (Fin 4)) = 0 := by
  funext i
  fin_cases i <;> simp [ambientTorusPoint]

theorem ambientTorusPoint_add
    (m n : ℤ) (x y : UnitAddTorus (Fin 4)) :
    ambientTorusPoint m n (x + y) =
      ambientTorusPoint m n x + ambientTorusPoint m n y := by
  funext i
  fin_cases i <;>
    simp [ambientTorusPoint] <;>
    abel

def toAmbientTorus (m n : ℤ) : Group →* AmbientTorus.Torus where
  toFun g := fun i =>
    AddCircle.toCircle (ambientTorusPoint m n g.toAdd i)
  map_one' := by
    funext i
    change AddCircle.toCircle (ambientTorusPoint m n 0 i) = 1
    rw [ambientTorusPoint_zero]
    simp
  map_mul' g h := by
    funext i
    change
      AddCircle.toCircle
          (ambientTorusPoint m n (g.toAdd + h.toAdd) i) =
        AddCircle.toCircle (ambientTorusPoint m n g.toAdd i) *
          AddCircle.toCircle (ambientTorusPoint m n h.toAdd i)
    rw [ambientTorusPoint_add, Pi.add_apply, AddCircle.toCircle_add]

/-- The actual physical compact torus homomorphism into `SU(6)`. -/
def embedding (m n : ℤ) : Group →* ActualRestriction.SU6 :=
  AmbientTorus.toSU6MonoidHom.comp (toAmbientTorus m n)

theorem toAmbientTorus_eq_ofDiagonalPoint
    (m n : ℤ) (x : UnitAddTorus (Fin 4)) :
    toAmbientTorus m n (Multiplicative.ofAdd x) =
      AmbientTorus.ofDiagonalPoint (physicalDiagonalPoint m n x) := by
  funext i
  apply Subtype.ext
  fin_cases i <;> rfl

theorem embedding_ofAdd
    (m n : ℤ) (x : UnitAddTorus (Fin 4)) :
    embedding m n (Multiplicative.ofAdd x) =
      (physicalDiagonalPoint m n x).toSU6 := by
  change
    (AmbientTorus.diagonalPoint
      (toAmbientTorus m n (Multiplicative.ofAdd x))).toSU6 = _
  rw [toAmbientTorus_eq_ofDiagonalPoint,
    AmbientTorus.diagonalPoint_ofDiagonalPoint]

/-!
## Restriction and character equivalence
-/

def restrictVirtual
    (m n : ℤ) (chi : AmbientCharacterBridge.FiniteVirtualRepresentation) :
    FiniteVirtualGroupRepresentation Group :=
  PhysicalRestrictionBridge.restrictVirtual (embedding m n) chi

theorem restrictVirtual_character
    (m n : ℤ) (chi : AmbientCharacterBridge.FiniteVirtualRepresentation)
    (x : UnitAddTorus (Fin 4)) :
    FiniteVirtualGroupRepresentation.character (restrictVirtual m n chi)
        (Multiplicative.ofAdd x) =
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi
        (physicalDiagonalPoint m n x) := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp only [restrictVirtual, PhysicalRestrictionBridge.restrictVirtual,
        FiniteVirtualGroupRepresentation.character,
        VirtualGroupSummand.character, PhysicalRestrictionBridge.restrictSummand,
        AmbientCharacterBridge.finiteVirtualRestrictedCharacter,
        AmbientCharacterBridge.summandRestrictedCharacter]
      change
        (s.coeff : ℂ) * s.rep.rho.character
              (embedding m n (Multiplicative.ofAdd x)) +
            FiniteVirtualGroupRepresentation.character
              (restrictVirtual m n ss) (Multiplicative.ofAdd x) =
          (s.coeff : ℂ) *
              AmbientCharacterBridge.actualRestrictedCharacter s.rep
                (physicalDiagonalPoint m n x) +
            AmbientCharacterBridge.finiteVirtualRestrictedCharacter ss
              (physicalDiagonalPoint m n x)
      rw [embedding_ofAdd, ih]
      rfl

/-- The standard physical source hypothesis expressed as character
equivalence after restriction to the actual compact physical torus. -/
def IsSMTargetCharacterEquivalent
    (chi : AmbientCharacterBridge.FiniteVirtualRepresentation)
    (generations singlets m n : ℤ) : Prop :=
  FiniteVirtualGroupRepresentation.CharacterEquivalent
    (restrictVirtual m n chi) (target generations singlets)

theorem exactCharacterOnPhysicalTorus_of_characterEquivalent
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (generations singlets m n : ℤ)
    (hEquivalent : IsSMTargetCharacterEquivalent
      chi generations singlets m n) :
    IsExactSMCharacterOnPhysicalTorus
      (chi := chi) generations singlets m n := by
  intro x
  calc
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi
        (physicalDiagonalPoint m n x) =
      FiniteVirtualGroupRepresentation.character (restrictVirtual m n chi)
        (Multiplicative.ofAdd x) :=
      (restrictVirtual_character m n chi x).symm
    _ = FiniteVirtualGroupRepresentation.character
          (target generations singlets) (Multiplicative.ofAdd x) :=
      hEquivalent (Multiplicative.ofAdd x)
    _ = PhysicalTorusCharacterBridge.eval
          (exactSMCharacter generations singlets) x :=
      target_character generations singlets x

/-- Representation-theoretic hypercharge character rigidity source theorem: character equivalence between
an actual finite virtual `SU(6)` restriction and the explicit physical torus
target forces the standard pair for every nonzero generation count. -/
theorem eq_standard_of_virtualModel_characterEquivalent
    {chi : AmbientCharacterBridge.FiniteVirtualRepresentation}
    (M : AmbientCharacterBridge.VirtualAmbientLaurentModel chi)
    (generations singlets m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hEquivalent : IsSMTargetCharacterEquivalent
      chi generations singlets m n) :
    m = -2 ∧ n = 3 :=
  PhysicalTorusCharacterBridge.eq_standard_of_virtualModel_characterOnPhysicalTorus
    M generations singlets m n hGenerations
      (exactCharacterOnPhysicalTorus_of_characterEquivalent
        generations singlets m n hEquivalent)

/-- Continuous-unitary physical-source specialization of the
representation-theoretic character-equivalence theorem. -/
theorem eq_standard_of_continuousUnitarySource_characterEquivalent
    {A : Type*}
    (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource A)
    (generations singlets m n : ℤ)
    (hGenerations : generations ≠ 0)
    (hEquivalent : IsSMTargetCharacterEquivalent
      source.toVirtual generations singlets m n) :
    m = -2 ∧ n = 3 :=
  eq_standard_of_virtualModel_characterEquivalent source.ambientLaurentModel
    generations singlets m n hGenerations hEquivalent

end
end PhysicalSMTorusTarget
end GUT
