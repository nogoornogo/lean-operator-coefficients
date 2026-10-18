import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedEvaluation
import Physics.FieldTheory.Mass.UnitaryVirtualRealization

open Math

/-!
# Actual charged source characters on an arbitrary physical torus

For an integral physical cocharacter pair `(m,n)`, this file reconstructs the
product action of the compact physical four-torus and an ordinary Abelian
residual group on every actual full charge sector of a continuous-unitary
`SU(6)` representation.  Its trace is the faithful physical
weight-and-charge evaluator.
-/

namespace GUT
namespace PhysicalChargedCharacterBridge

open CompactEmbeddingClassification
open ContinuousUnitaryWeightDecomposition
open FiniteAbelianChargeSectors
open PhysicalChargeResolvedBridge
open PhysicalChargeResolvedEvaluation
open PhysicalRestrictionBridge
open StandardPhysicalCharacterBridge
open StandardPhysicalSource
open UnitaryVirtualRealization

noncomputable section

universe u

abbrev ChargeLabel (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-- The actual product-group action on one full residual-charge sector at an
arbitrary physical cocharacter pair. -/
def chargedPhysicalRho
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation ℂ
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) s.rep.V where
  toFun g :=
    LinearMap.lsmul ℂ s.rep.V (((s.offset.toMul g.2 : Circle) : ℂ)) *
      s.rep.rho (PhysicalSMTorusTarget.embedding m n g.1)
  map_one' := by
    ext v
    simp
  map_mul' g k := by
    ext v
    simp only [Prod.snd_mul, map_mul]
    simp [smul_smul, mul_assoc]
    rw [mul_comm
      (((s.offset.toMul g.2 : Circle) : ℂ))
      (((s.offset.toMul k.2 : Circle) : ℂ))]

def chargedPhysicalRepresentation
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualGroupRepresentation
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) where
  V := s.rep.V
  rho := chargedPhysicalRho m n s

/-- The reconstructed physical-torus and residual-character action is
unitary. -/
theorem chargedPhysicalRho_unitary
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    IsUnitaryRepresentation (chargedPhysicalRho m n s) := by
  intro g v w
  change
    inner ℂ
        (((s.offset.toMul g.2 : Circle) : ℂ) •
          s.rep.rho (PhysicalSMTorusTarget.embedding m n g.1) v)
        (((s.offset.toMul g.2 : Circle) : ℂ) •
          s.rep.rho (PhysicalSMTorusTarget.embedding m n g.1) w) =
      inner ℂ v w
  calc
    _ = inner ℂ
        (s.rep.rho (PhysicalSMTorusTarget.embedding m n g.1) v)
        (s.rep.rho (PhysicalSMTorusTarget.embedding m n g.1) w) := by
      rw [inner_smul_left, inner_smul_right,
        ← Circle.coe_inv_eq_conj]
      simp
    _ = inner ℂ v w :=
      s.rep.unitary (PhysicalSMTorusTarget.embedding m n g.1) v w

/-- Bundle the reconstructed charged action together with the invariant
Hermitian inner product inherited from the original `SU(6)` representation. -/
def chargedPhysicalUnitaryRepresentation
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualUnitaryGroupRepresentation
      (PhysicalChargeResolvedEvaluation.CombinedGroup H) where
  V := s.rep.V
  rho := chargedPhysicalRho m n s
  unitary := chargedPhysicalRho_unitary m n s

theorem chargedPhysicalUnitaryRepresentation_toActual
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    (chargedPhysicalUnitaryRepresentation m n s).toActualGroupRepresentation =
      chargedPhysicalRepresentation m n s := by
  rfl

/-- Pulling an ambient weight eigenvalue back to the arbitrary physical
four-torus gives its restricted Fourier monomial. -/
theorem exponent_eval_physicalAmbient
    (m n : ℤ) (e : AmbientWeightLattice.Exponent)
    (x : UnitAddTorus (Fin 4)) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (PhysicalSMTorusTarget.toAmbientTorus m n
            (Multiplicative.ofAdd x))).toTorusVec =
      UnitAddTorus.mFourier
        (PhysicalTorusCharacterBridge.restrictExponent m n e) x := by
  rw [PhysicalSMTorusTarget.toAmbientTorus_eq_ofDiagonalPoint,
    AmbientTorus.diagonalPoint_ofDiagonalPoint]
  change
    AmbientLaurent.Exponent.eval e
        (AmbientLaurent.DiagonalPoint.ofUnitAddTorus
          (PhysicalTorusCharacterBridge.ambientTorusPoint m n x)).toTorusVec =
      _
  rw [AmbientLaurent.DiagonalPoint.toTorusVec_ofUnitAddTorus,
    AmbientLaurent.Exponent.eval_torusVecOfUnitAddTorus,
    PhysicalTorusCharacterBridge.mFourier_ambientTorusPoint]

/-- The canonical ambient weight basis diagonalizes the reconstructed
product-group action with the expected physical weight and residual charge. -/
theorem chargedPhysicalRho_action_on_weightBasis
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H)
    (i : (chargedWeightBasis s).ι) :
    chargedPhysicalRho m n s (Multiplicative.ofAdd x, h)
        ((chargedWeightBasis s).basis i) =
      keyMonoidHom
          (physicalProjectKey m n s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) •
        (chargedWeightBasis s).basis i := by
  let B := chargedWeightBasis s
  have hBasis := B.action_on_basis
    (PhysicalSMTorusTarget.toAmbientTorus m n (Multiplicative.ofAdd x)) i
  change
    s.rep.rho
        (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x))
        (B.basis i) =
      AmbientLaurent.Exponent.eval (B.weight i)
          (AmbientTorus.diagonalPoint
            (PhysicalSMTorusTarget.toAmbientTorus m n
              (Multiplicative.ofAdd x))).toTorusVec •
        B.basis i at hBasis
  change
    ((s.offset.toMul h : Circle) : ℂ) •
        s.rep.rho
          (PhysicalSMTorusTarget.embedding m n (Multiplicative.ofAdd x))
          (B.basis i) = _
  rw [hBasis, smul_smul, exponent_eval_physicalAmbient,
    keyMonoidHom_apply]
  change
    (((s.offset.toMul h : Circle) : ℂ) *
        UnitAddTorus.mFourier
          (PhysicalTorusCharacterBridge.restrictExponent m n (B.weight i)) x) •
        B.basis i =
      (UnitAddTorus.mFourier
          (PhysicalTorusCharacterBridge.restrictExponent m n (B.weight i)) x *
        ((s.offset.toMul h : Circle) : ℂ)) • B.basis i
  rw [mul_comm]

theorem chargedPhysicalRho_character_eq_weightSum
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (chargedPhysicalRho m n s).character (Multiplicative.ofAdd x, h) =
      ∑ i : (chargedWeightBasis s).ι,
        keyMonoidHom
          (physicalProjectKey m n s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) := by
  unfold Representation.character
  exact WeightTheory.trace_eq_sum_of_basis_eigen
    (chargedWeightBasis s).basis
    (chargedPhysicalRho m n s (Multiplicative.ofAdd x, h))
    (fun i =>
      keyMonoidHom
        (physicalProjectKey m n s.offset
          ((chargedWeightBasis s).weight i))
        (Multiplicative.ofAdd x, h))
    (chargedPhysicalRho_action_on_weightBasis m n s x h)

theorem eval_projectedWeightBasis
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    PhysicalChargeResolvedEvaluation.eval
        (Finsupp.mapDomain (physicalProjectKey m n s.offset)
          (chargedWeightBasis s).poly) x h =
      ∑ i : (chargedWeightBasis s).ι,
        keyMonoidHom
          (physicalProjectKey m n s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) := by
  change
    PhysicalChargeResolvedEvaluation.evalAddHom x h
      (Finsupp.mapDomain (physicalProjectKey m n s.offset)
        (∑ i : (chargedWeightBasis s).ι,
          Finsupp.single ((chargedWeightBasis s).weight i) 1)) = _
  rw [Finsupp.mapDomain_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finsupp.mapDomain_single]
  simp [PhysicalChargeResolvedEvaluation.evalAddHom,
    PhysicalChargeResolvedEvaluation.eval]

/-- The trace on one actual charged sector is exactly its physical resolved
finite-weight evaluator. -/
theorem chargedPhysicalRho_character
    {H : Type u} [CommGroup H]
    (m n : ℤ) (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (chargedPhysicalRho m n s).character (Multiplicative.ofAdd x, h) =
      PhysicalChargeResolvedEvaluation.eval
        (Finsupp.mapDomain (physicalProjectKey m n s.offset)
          s.rep.ambientLaurentModel.poly) x h := by
  rw [← chargedWeightBasis_poly s]
  exact (chargedPhysicalRho_character_eq_weightSum m n s x h).trans
    (eval_projectedWeightBasis m n s x h).symm

/-- Assemble the actual product-group representations of every charged
source sector, retaining the original virtual coefficients. -/
def sourceProductRepresentation
    {H : Type u} [CommGroup H] (m n : ℤ) :
    FiniteChargedContinuousUnitarySource (ChargeLabel H) →
      FiniteVirtualGroupRepresentation
        (PhysicalChargeResolvedEvaluation.CombinedGroup H)
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := chargedPhysicalRepresentation m n s } ::
        sourceProductRepresentation m n source

/-- Retain the unitary certificate on every summand of the reconstructed
physical source. -/
def sourceUnitaryRepresentation
    {H : Type u} [CommGroup H] (m n : ℤ) :
    FiniteChargedContinuousUnitarySource (ChargeLabel H) →
      FiniteUnitaryVirtualRepresentation
        (PhysicalChargeResolvedEvaluation.CombinedGroup H)
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := chargedPhysicalUnitaryRepresentation m n s } ::
        sourceUnitaryRepresentation m n source

/-- Forgetting the unitary certificates recovers the existing actual
product-group virtual representation exactly. -/
theorem sourceUnitaryRepresentation_toFiniteVirtual
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    FiniteUnitaryVirtualRepresentation.toFiniteVirtual
        (sourceUnitaryRepresentation m n source) =
      sourceProductRepresentation m n source := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      simp only [sourceUnitaryRepresentation, sourceProductRepresentation,
        FiniteUnitaryVirtualRepresentation.toFiniteVirtual]
      rw [ih, chargedPhysicalUnitaryRepresentation_toActual]

/-- The assembled actual trace equals the canonical physical
weight-and-charge resolved evaluator. -/
theorem sourceProductRepresentation_character
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (sourceProductRepresentation m n source)
        (Multiplicative.ofAdd x, h) =
      PhysicalChargeResolvedEvaluation.eval
        (sourcePhysicalResolvedCharacter m n source) x h := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) *
              (chargedPhysicalRho m n s).character
                (Multiplicative.ofAdd x, h) +
            FiniteVirtualGroupRepresentation.character
              (sourceProductRepresentation m n source)
              (Multiplicative.ofAdd x, h) =
          PhysicalChargeResolvedEvaluation.eval
            (s.coeff •
                Finsupp.mapDomain (physicalProjectKey m n s.offset)
                  s.rep.ambientLaurentModel.poly +
              sourcePhysicalResolvedCharacter m n source) x h
      rw [chargedPhysicalRho_character, ih,
        PhysicalChargeResolvedEvaluation.eval_add,
        PhysicalChargeResolvedEvaluation.eval_zsmul]

/-- The reconstructed actual source is a character model for the canonical
physical resolved `Finsupp`. -/
theorem sourceProductRepresentation_isCharacterModel
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    PhysicalChargeResolvedEvaluation.IsCharacterModel
      (sourceProductRepresentation m n source)
      (sourcePhysicalResolvedCharacter m n source) :=
  sourceProductRepresentation_character m n source

/-- The canonical positive and negative Hilbert-space aggregates realize the
actual charged source character as an ultraviolet mass index. -/
theorem canonicalUltravioletIndex_characterEquivalent
    {H : Type u} [CommGroup H]
    (m n : ℤ)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (EquivariantMassIndex.ultravioletIndex
        (rhoV₀ :=
          (FiniteUnitaryVirtualRepresentation.positive
            (sourceUnitaryRepresentation m n source)).rho)
        (rhoW₀ :=
          (FiniteUnitaryVirtualRepresentation.negative
            (sourceUnitaryRepresentation m n source)).rho))
      (sourceProductRepresentation m n source) := by
  rw [← sourceUnitaryRepresentation_toFiniteVirtual m n source]
  exact
    FiniteUnitaryVirtualRepresentation.ultravioletIndex_characterEquivalent
      (sourceUnitaryRepresentation m n source)

end

end PhysicalChargedCharacterBridge
end GUT
