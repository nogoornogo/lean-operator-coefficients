import GUT.SU6.SelectionRules.Models.PhysicalChargedCharacterBridge
import Physics.FieldTheory.Mass.UnitaryBlockMass

open Math

/-!
# Structural realization of a physical light spectrum

The faithful physical resolved target is a finite virtual sum of
one-dimensional unitary characters.  This file retains those unitary
certificates and turns actual representation equivalences of the unmatched
kernel and cokernel into the character equivalence consumed by the mass-index
bridge.
-/

namespace GUT
namespace PhysicalLightSpectrumBridge

open CompactEmbeddingClassification
open EquivariantMassIndex
open PhysicalChargeResolvedBridge
open PhysicalChargeResolvedEvaluation
open PhysicalRestrictionBridge
open UnitaryVirtualRealization

noncomputable section

universe u

/-- Every physical weight-and-residual-charge character takes values on the
complex unit circle. -/
theorem norm_keyMonoidHom
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H))
    (g : CombinedGroup H) :
    ‖keyMonoidHom key g‖ = 1 := by
  rcases g with ⟨x, h⟩
  rw [keyMonoidHom_apply, norm_mul, Circle.norm_coe]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one, one_mul]

/-- The one-dimensional realization of a physical resolved key is unitary. -/
theorem weightRho_unitary
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    IsUnitaryRepresentation (weightRho key) := by
  intro g v w
  change
    inner ℂ ((keyMonoidHom key g) • v) ((keyMonoidHom key g) • w) =
      inner ℂ v w
  rw [inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul, norm_keyMonoidHom]
  norm_num

/-- The one-dimensional physical key representation with its invariant
Hermitian form retained. -/
def weightUnitaryRepresentation
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := ℂ
  rho := weightRho key
  unitary := weightRho_unitary key

theorem weightUnitaryRepresentation_toActual
    {H : Type u} [CommGroup H]
    (key : PhysicalResolvedKey (ChargeLabel H)) :
    (weightUnitaryRepresentation key).toActualGroupRepresentation =
      weightRepresentation key := by
  rfl

/-- Unitarly realize every nonzero coefficient of a physical resolved
character. -/
def unitaryOfCharacter
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    FiniteUnitaryVirtualRepresentation (CombinedGroup H) :=
  p.support.toList.map fun key =>
    { coeff := p key
      rep := weightUnitaryRepresentation key }

/-- Forgetting unitary certificates recovers the faithful evaluator's
existing finite virtual realization exactly. -/
theorem unitaryOfCharacter_toFiniteVirtual
    {H : Type u} [CommGroup H]
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :
    FiniteUnitaryVirtualRepresentation.toFiniteVirtual
        (unitaryOfCharacter p) =
      PhysicalChargeResolvedEvaluation.ofCharacter p := by
  classical
  let unitarySummand := fun key : PhysicalResolvedKey (ChargeLabel H) =>
    UnitaryVirtualSummand.mk (p key) (weightUnitaryRepresentation key)
  let summand := fun key : PhysicalResolvedKey (ChargeLabel H) =>
    VirtualGroupSummand.mk (p key) (weightRepresentation key)
  have hList (l : List (PhysicalResolvedKey (ChargeLabel H))) :
      FiniteUnitaryVirtualRepresentation.toFiniteVirtual
          (l.map unitarySummand) = l.map summand := by
    induction l with
    | nil => rfl
    | cons key keys ih =>
        simp only [List.map_cons,
          FiniteUnitaryVirtualRepresentation.toFiniteVirtual]
        rw [ih]
        change
          { coeff := p key
            rep := (weightUnitaryRepresentation key).toActualGroupRepresentation } ::
              keys.map summand =
            { coeff := p key
              rep := weightRepresentation key } :: keys.map summand
        rw [weightUnitaryRepresentation_toActual]
  exact hList p.support.toList

/-- A structural light-spectrum certificate identifies the actual unmatched
mode spaces with the positive and negative unitary target aggregates. -/
abbrev LightSpectrumEquiv
    {H : Type u} [CommGroup H]
    {V W : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    {rhoV : Representation ℂ (CombinedGroup H) V}
    {rhoW : Representation ℂ (CombinedGroup H) W}
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW)
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :=
  FiniteUnitaryVirtualRepresentation.LightIndexEquiv
    f hW (unitaryOfCharacter p)

/-- Mode-space representation equivalences imply the exact light-character
identification required by the physical mass-index bridge. -/
theorem lightIndex_characterEquivalent_of_equiv
    {H : Type u} [CommGroup H]
    {V W : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    {rhoV : Representation ℂ (CombinedGroup H) V}
    {rhoW : Representation ℂ (CombinedGroup H) W}
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW)
    (p : PhysicalResolvedCharacter (ChargeLabel H))
    (e : LightSpectrumEquiv f hW p) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex f hW)
      (PhysicalChargeResolvedEvaluation.ofCharacter p) := by
  rw [← unitaryOfCharacter_toFiniteVirtual p]
  exact
    FiniteUnitaryVirtualRepresentation.lightIndex_characterEquivalent_of_equiv
      f hW (unitaryOfCharacter p) e

/-!
## Constructing the mass certificate from a block decomposition
-/

/-- A physical light-plus-heavy decomposition: the ultraviolet source and
target are unitarily equivalent to the positive and negative resolved target
aggregates plus one common paired representation. -/
abbrev BlockDecomposition
    {H : Type u} [CommGroup H]
    (A B : ActualUnitaryGroupRepresentation (CombinedGroup H))
    (p : PhysicalResolvedCharacter (ChargeLabel H)) :=
  UnitaryBlockMass.FiniteUnitaryVirtualRepresentation.BlockDecomposition
    A B (unitaryOfCharacter p)

namespace BlockDecomposition

/-- The equivariant mass map canonically constructed from a physical block
decomposition. -/
def massMap
    {H : Type u} [CommGroup H]
    {A B : ActualUnitaryGroupRepresentation (CombinedGroup H)}
    {p : PhysicalResolvedCharacter (ChargeLabel H)}
    (d : BlockDecomposition A B p) :
    Representation.IntertwiningMap A.rho B.rho :=
  UnitaryBlockMass.FiniteUnitaryVirtualRepresentation.BlockDecomposition.massMap d

/-- A physical block decomposition supplies the exact kernel/cokernel
certificate expected by the mass-spectrum bridge. -/
def lightSpectrumEquiv
    {H : Type u} [CommGroup H]
    {A B : ActualUnitaryGroupRepresentation (CombinedGroup H)}
    {p : PhysicalResolvedCharacter (ChargeLabel H)}
    (d : BlockDecomposition A B p) :
    LightSpectrumEquiv d.massMap B.unitary p :=
  UnitaryBlockMass.FiniteUnitaryVirtualRepresentation.BlockDecomposition.lightIndexEquiv d

end BlockDecomposition

end

end PhysicalLightSpectrumBridge
end GUT
