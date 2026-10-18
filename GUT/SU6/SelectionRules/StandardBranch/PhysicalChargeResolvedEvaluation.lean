import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedBridge
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open Math

/-!
# Faithful evaluation of physical charge-resolved characters

The physical normal form has keys consisting of an arbitrary integral weight
of the compact four-torus and an independent character of the residual
Abelian group.  Distinct such pairs define distinct characters of the product
group.  Dedekind linear independence therefore makes joint evaluation
faithful, including for finite residual groups.
-/

open scoped BigOperators

namespace GUT
namespace PhysicalChargeResolvedEvaluation

open PhysicalChargeResolvedBridge
open PhysicalRestrictionBridge

noncomputable section

universe u

abbrev CompactTorus := Multiplicative (UnitAddTorus (Fin 4))
abbrev CombinedGroup (H : Type u) := CompactTorus × H
abbrev ChargeLabel (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-- The product-group character associated with one physical torus weight
and one residual charge. -/
def keyMonoidHom
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    CombinedGroup H →* ℂ :=
  (PhysicalTorusCharacterBridge.Fourier.exponentMonoidHom key.1).coprod
    (StandardSMCharacterTarget.chargeMonoidHom key.2)

@[simp]
theorem keyMonoidHom_apply
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H))
    (x : CompactTorus) (h : H) :
    keyMonoidHom key (x, h) =
      UnitAddTorus.mFourier key.1 x.toAdd *
        ((key.2.toMul h : Circle) : ℂ) :=
  rfl

theorem keyMonoidHom_injective
    {H : Type u} [CommGroup H] :
    Function.Injective
      (keyMonoidHom (H := H) :
        PhysicalResolvedKey (ChargeLabel H) → CombinedGroup H →* ℂ) := by
  rintro ⟨e, q⟩ ⟨f, r⟩ h
  apply Prod.ext
  · apply PhysicalTorusCharacterBridge.Fourier.exponentMonoidHom_injective
    apply MonoidHom.ext
    intro x
    have hx := congrArg
      (fun phi : CombinedGroup H →* ℂ => phi (x, 1)) h
    simpa [keyMonoidHom, StandardSMCharacterTarget.chargeMonoidHom,
      StandardSMCharacterTarget.circleCoeMonoidHom] using hx
  · apply Additive.toMul.injective
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    have ha := congrArg
      (fun phi : CombinedGroup H →* ℂ => phi (1, a)) h
    change
      StandardSMCharacterTarget.circleCoeMonoidHom (q.toMul a) =
        StandardSMCharacterTarget.circleCoeMonoidHom (r.toMul a)
    simpa [keyMonoidHom,
      StandardSMCharacterTarget.chargeMonoidHom] using ha

theorem linearIndependent_keyMonoidHom
    {H : Type u} [CommGroup H] :
    LinearIndependent ℂ
      (fun key : PhysicalResolvedKey (ChargeLabel H) =>
        (keyMonoidHom key : CombinedGroup H → ℂ)) := by
  exact (linearIndependent_monoidHom (CombinedGroup H) ℂ).comp
    keyMonoidHom keyMonoidHom_injective

/-- Joint evaluation on the physical compact torus and residual group. -/
def eval
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) : ℂ :=
  p.sum fun key c =>
    (c : ℂ) * keyMonoidHom key (Multiplicative.ofAdd x, h)

def evalAddHom
    {H : Type u} [CommGroup H]
    (x : UnitAddTorus (Fin 4)) (h : H) :
    PhysicalResolvedCharacter (ChargeLabel H) →+ ℂ where
  toFun p := eval p x h
  map_zero' := by simp [eval]
  map_add' p q := by
    classical
    rw [eval, eval, eval, Finsupp.sum_add_index]
    · intro key _hkey
      simp
    · intro key _hkey a b
      rw [Int.cast_add]
      ring

@[simp]
theorem evalAddHom_apply
    {H : Type u} [CommGroup H]
    (x : UnitAddTorus (Fin 4)) (h : H)
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    evalAddHom x h p = eval p x h :=
  rfl

/-- Evaluation at a fixed product-group point is additive. -/
theorem eval_add
    {H : Type u} [CommGroup H]
    (p q : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (p + q) x h = eval p x h + eval q x h := by
  classical
  rw [eval, eval, eval, Finsupp.sum_add_index]
  · intro key _hkey
    simp
  · intro key _hkey a b
    rw [Int.cast_add]
    ring

/-- Integral virtual multiplicity becomes scalar multiplication after
evaluation. -/
theorem eval_zsmul
    {H : Type u} [CommGroup H]
    (n : ℤ) (p : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (n • p) x h = (n : ℂ) * eval p x h := by
  change evalAddHom x h (n • p) = _
  rw [map_zsmul, zsmul_eq_mul]
  rfl

def toComplex
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    PhysicalResolvedKey (ChargeLabel H) →₀ ℂ :=
  Finsupp.mapRange (fun c : ℤ => (c : ℂ)) (by simp) p

@[simp]
theorem toComplex_apply
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H))
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    toComplex p key = (p key : ℂ) := by
  simp [toComplex]

theorem eval_eq_linearCombination
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    Finsupp.linearCombination ℂ
        (fun key : PhysicalResolvedKey (ChargeLabel H) =>
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

/-- Equality of all product-group evaluations determines every integral
weight-and-charge coefficient. -/
theorem eval_faithful
    {H : Type u} [CommGroup H]
    (p q : PhysicalResolvedCharacter (ChargeLabel H))
    (h : ∀ (x : UnitAddTorus (Fin 4)) (a : H),
      eval p x a = eval q x a) :
    p = q := by
  have hLinear :
      Finsupp.linearCombination ℂ
          (fun key : PhysicalResolvedKey (ChargeLabel H) =>
            (keyMonoidHom key : CombinedGroup H → ℂ))
          (toComplex p) =
        Finsupp.linearCombination ℂ
          (fun key : PhysicalResolvedKey (ChargeLabel H) =>
            (keyMonoidHom key : CombinedGroup H → ℂ))
          (toComplex q) := by
    rw [eval_eq_linearCombination p, eval_eq_linearCombination q]
    funext g
    exact h g.1.toAdd g.2
  have hComplex : toComplex p = toComplex q :=
    linearIndependent_keyMonoidHom.finsuppLinearCombination_injective hLinear
  ext key
  exact Int.cast_injective (α := ℂ) (by
    simpa using congrArg
      (fun r : PhysicalResolvedKey (ChargeLabel H) →₀ ℂ => r key)
      hComplex)

/-!
## Actual finite virtual realization
-/

def weightRho
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    Representation ℂ (CombinedGroup H) ℂ where
  toFun g := LinearMap.lsmul ℂ ℂ (keyMonoidHom key g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem weightRho_character
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H))
    (g : CombinedGroup H) :
    (weightRho key).character g = keyMonoidHom key g := by
  change LinearMap.trace ℂ ℂ
    (LinearMap.lsmul ℂ ℂ (keyMonoidHom key g)) = _
  rw [show LinearMap.lsmul ℂ ℂ (keyMonoidHom key g) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
        (keyMonoidHom key g) by
    apply LinearMap.ext
    intro z
    simp [mul_comm]]
  exact LinearMap.trace_smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) _

def weightRepresentation
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    ActualGroupRepresentation (CombinedGroup H) where
  V := ℂ
  rho := weightRho key

def ofCharacter
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    FiniteVirtualGroupRepresentation (CombinedGroup H) :=
  p.support.toList.map fun key =>
    { coeff := p key
      rep := weightRepresentation key }

theorem character_ofCharacter
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character (ofCharacter p)
        (Multiplicative.ofAdd x, h) = eval p x h := by
  classical
  let summand : PhysicalResolvedKey (ChargeLabel H) →
      VirtualGroupSummand (CombinedGroup H) := fun key =>
    { coeff := p key
      rep := weightRepresentation key }
  have hList (l : List (PhysicalResolvedKey (ChargeLabel H))) :
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

/-- An actual virtual representation realizes a physical resolved
character when their evaluations agree on the whole product group. -/
def IsCharacterModel
    {H : Type u} [CommGroup H]
    (source : FiniteVirtualGroupRepresentation (CombinedGroup H))
    (p : PhysicalResolvedCharacter (ChargeLabel H)) : Prop :=
  ∀ (x : UnitAddTorus (Fin 4)) (h : H),
    FiniteVirtualGroupRepresentation.character source
        (Multiplicative.ofAdd x, h) = eval p x h

theorem ofCharacter_isCharacterModel
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    IsCharacterModel (ofCharacter p) p :=
  character_ofCharacter p

/-- Character equivalence between two faithfully modeled sources forces
equality of their physical resolved coefficients. -/
theorem character_eq_of_models_of_characterEquivalent
    {H : Type u} [CommGroup H]
    {source target : FiniteVirtualGroupRepresentation (CombinedGroup H)}
    {p q : PhysicalResolvedCharacter (ChargeLabel H)}
    (hSource : IsCharacterModel source p)
    (hTarget : IsCharacterModel target q)
    (hEquivalent :
      FiniteVirtualGroupRepresentation.CharacterEquivalent source target) :
    p = q := by
  apply eval_faithful
  intro x h
  rw [← hSource x h, ← hTarget x h]
  exact hEquivalent (Multiplicative.ofAdd x, h)

end

end PhysicalChargeResolvedEvaluation
end GUT
