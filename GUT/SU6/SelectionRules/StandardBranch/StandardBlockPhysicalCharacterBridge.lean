import GUT.SU6.SelectionRules.StandardBranch.StandardBlockChargeProjection
import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalCharacterBridge
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Tactic

open Math

/-!
# Actual product characters for a standard block-gauge lift

This file supplies the trace interpretation of the raw block-charge
projection in standard diagonal coordinates.  A determinant-one block triple
with color and weak coefficients `(c,w)` is sent to the ambient torus point
`(c,c,c,w,w)`.  The hypercharge character rigidity weight eigenvalue is therefore exactly the additive
charge `colorDegree * c + weakDegree * w`, before normalization of the
rank-five Laurent weight.

The later geometric bridge may conjugate an actual semisimple embedding classification embedding and its
centralizer into these standard coordinates.  Keeping that conjugacy input
separate prevents the algebraic character calculation from silently assuming
that an arbitrary physical embedding is already diagonal.
-/

namespace GUT
namespace StandardBlockPhysicalCharacterBridge

open scoped BigOperators

open ContinuousUnitaryWeightDecomposition
open FiniteAbelianChargeSectors
open PhysicalRestrictionBridge
open StandardAbelianCharge
open StandardBlockChargeProjection
open StandardBlockGaugeCancellation
open StandardPhysicalSource
open StandardSMCharacterTarget
open StandardPhysicalCharacterBridge

noncomputable section

universe u

abbrev CompactTorus := StandardSMCharacterTarget.CompactTorus
abbrev CombinedGroup (H : Type u) :=
  StandardSMCharacterTarget.CombinedGroup H
abbrev ChargeLabel (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-!
## The diagonal block torus
-/

/-- Put the color coefficient in the first three ambient coordinates and the
weak coefficient in the last two independent coordinates. -/
def blockAmbientHom :
    CompactBlockCentralizer.Group →* AmbientTorus.Torus where
  toFun p := fun i => if i.1 < 3 then p.1.1 else p.1.2.1
  map_one' := by
    funext i
    fin_cases i <;> rfl
  map_mul' p q := by
    funext i
    fin_cases i <;> rfl

@[simp]
theorem blockAmbientHom_color_zero
    (p : CompactBlockCentralizer.Group) :
    blockAmbientHom p 0 = p.1.1 :=
  rfl

@[simp]
theorem blockAmbientHom_color_one
    (p : CompactBlockCentralizer.Group) :
    blockAmbientHom p 1 = p.1.1 :=
  rfl

@[simp]
theorem blockAmbientHom_color_two
    (p : CompactBlockCentralizer.Group) :
    blockAmbientHom p 2 = p.1.1 :=
  rfl

@[simp]
theorem blockAmbientHom_weak_three
    (p : CompactBlockCentralizer.Group) :
    blockAmbientHom p 3 = p.1.2.1 :=
  rfl

@[simp]
theorem blockAmbientHom_weak_four
    (p : CompactBlockCentralizer.Group) :
    blockAmbientHom p 4 = p.1.2.1 :=
  rfl

/-- A residual block-gauge homomorphism as an ambient diagonal-torus
homomorphism. -/
def residualBlockAmbientHom
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) :
    H →* AmbientTorus.Torus :=
  blockAmbientHom.comp gauge

/-- Evaluation of a raw hypercharge character rigidity weight on the diagonal block lift is exactly the
multiplicative character underlying `blockCharge`. -/
theorem exponent_eval_residualBlockAmbient
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (e : AmbientWeightLattice.Exponent) (h : H) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (residualBlockAmbientHom gauge h)).toTorusVec =
      (((blockCharge (colorCharge gauge) (weakCharge gauge) e).toMul h :
        Circle) : ℂ) := by
  rw [AmbientTorus.exponent_eval_diagonalPoint]
  have hCircle :
      CircleTorusCharacterLattice.torusCharacter e
          (residualBlockAmbientHom gauge h) =
        (blockCharge (colorCharge gauge) (weakCharge gauge) e).toMul h := by
    simp only [CircleTorusCharacterLattice.torusCharacter_apply]
    change
      (∏ i : Fin 5,
        (if i.1 < 3 then (gauge h).1.1 else (gauge h).1.2.1) ^ e i) =
        ((blockCharge (colorCharge gauge) (weakCharge gauge) e).toMul h :
          Circle)
    simp [blockCharge, colorDegree, weakDegree, colorCharge, weakCharge,
      colorCharacter, weakCharacter, colorProjection, weakProjection,
      zpow_add, Fin.prod_univ_succ]
    simp only [mul_assoc]
  exact congrArg (fun z : Circle => (z : ℂ)) hCircle

/-!
## Actual diagonal product representations
-/

/-- Combine the standard physical four-torus with a residual block-gauge
lift inside the ambient diagonal torus. -/
def combinedBlockAmbientHom
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) :
    CombinedGroup H →* AmbientTorus.Torus :=
  (PhysicalSMTorusTarget.toAmbientTorus (-2) 3).coprod
    (residualBlockAmbientHom gauge)

def combinedBlockGaugeHom
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) :
    CombinedGroup H →* ActualRestriction.SU6 :=
  AmbientTorus.toSU6MonoidHom.comp (combinedBlockAmbientHom gauge)

theorem exponent_eval_combinedBlockAmbient
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (e : AmbientWeightLattice.Exponent)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (combinedBlockAmbientHom gauge
            (Multiplicative.ofAdd x, h))).toTorusVec =
      UnitAddTorus.mFourier (standardExponent (normalizeWeight e)) x *
        (((blockCharge (colorCharge gauge) (weakCharge gauge) e).toMul h :
          Circle) : ℂ) := by
  rw [combinedBlockAmbientHom, MonoidHom.coprod_apply,
    exponent_eval_mul, exponent_eval_physicalAmbient,
    exponent_eval_residualBlockAmbient, standardExponent_normalizeWeight]

/-- The product representation carried by one external character sector when
the residual gauge part is the standard diagonal block lift. -/
def blockChargedProductRho
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation ℂ (CombinedGroup H) s.rep.V where
  toFun g :=
    LinearMap.lsmul ℂ s.rep.V (((s.offset.toMul g.2 : Circle) : ℂ)) *
      s.rep.rho (combinedBlockGaugeHom gauge g)
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

def blockChargedProductRepresentation
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualGroupRepresentation (CombinedGroup H) where
  V := s.rep.V
  rho := blockChargedProductRho gauge s

def blockChargedWeightBasis
    {H : Type u} [CommGroup H]
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    IntegerWeightBasis s.rep.rho :=
  integerWeightBasisOfContinuousUnitary s.rep.rho
    s.rep.unitary s.rep.continuous_action

theorem blockChargedWeightBasis_poly
    {H : Type u} [CommGroup H]
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    (blockChargedWeightBasis s).poly = s.rep.ambientLaurentModel.poly := by
  rfl

theorem blockChargedProductRho_action_on_weightBasis
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H)
    (i : (blockChargedWeightBasis s).ι) :
    blockChargedProductRho gauge s (Multiplicative.ofAdd x, h)
        ((blockChargedWeightBasis s).basis i) =
      keyMonoidHom
          (blockProjectKey (colorCharge gauge) (weakCharge gauge)
            ((blockChargedWeightBasis s).weight i, s.offset))
          (Multiplicative.ofAdd x, h) •
        (blockChargedWeightBasis s).basis i := by
  let B := blockChargedWeightBasis s
  have hBasis := B.action_on_basis
    (combinedBlockAmbientHom gauge (Multiplicative.ofAdd x, h)) i
  change
    s.rep.rho
        (combinedBlockGaugeHom gauge (Multiplicative.ofAdd x, h))
        (B.basis i) =
      AmbientLaurent.Exponent.eval (B.weight i)
          (AmbientTorus.diagonalPoint
            (combinedBlockAmbientHom gauge
              (Multiplicative.ofAdd x, h))).toTorusVec •
        B.basis i at hBasis
  change
    ((s.offset.toMul h : Circle) : ℂ) •
        s.rep.rho
          (combinedBlockGaugeHom gauge (Multiplicative.ofAdd x, h))
          (B.basis i) = _
  rw [hBasis, smul_smul, exponent_eval_combinedBlockAmbient]
  rw [keyMonoidHom_apply]
  change
    (((s.offset.toMul h : Circle) : ℂ) *
        (UnitAddTorus.mFourier
          (standardExponent (normalizeWeight (B.weight i))) x *
        (((blockCharge (colorCharge gauge) (weakCharge gauge)
          (B.weight i)).toMul h : Circle) : ℂ))) • B.basis i =
      (UnitAddTorus.mFourier
          (standardExponent (normalizeWeight (B.weight i))) x *
        ((((s.offset + blockCharge (colorCharge gauge) (weakCharge gauge)
          (B.weight i))).toMul h : Circle) : ℂ)) • B.basis i
  rw [chargeLabel_add_apply]
  congr 1
  ring

theorem blockChargedProductRho_character_eq_weightSum
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (blockChargedProductRho gauge s).character
        (Multiplicative.ofAdd x, h) =
      ∑ i : (blockChargedWeightBasis s).ι,
        keyMonoidHom
          (blockProjectKey (colorCharge gauge) (weakCharge gauge)
            ((blockChargedWeightBasis s).weight i, s.offset))
          (Multiplicative.ofAdd x, h) := by
  unfold Representation.character
  exact WeightTheory.trace_eq_sum_of_basis_eigen
    (blockChargedWeightBasis s).basis
    (blockChargedProductRho gauge s (Multiplicative.ofAdd x, h))
    (fun i => keyMonoidHom
      (blockProjectKey (colorCharge gauge) (weakCharge gauge)
        ((blockChargedWeightBasis s).weight i, s.offset))
      (Multiplicative.ofAdd x, h))
    (blockChargedProductRho_action_on_weightBasis gauge s x h)

theorem eval_blockResolved_weightBasis
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval
        (blockResolved (colorCharge gauge) (weakCharge gauge)
          (rawResolvedWithOffset s.offset (blockChargedWeightBasis s).poly))
        x h =
      ∑ i : (blockChargedWeightBasis s).ι,
        keyMonoidHom
          (blockProjectKey (colorCharge gauge) (weakCharge gauge)
            ((blockChargedWeightBasis s).weight i, s.offset))
          (Multiplicative.ofAdd x, h) := by
  change
    resolvedEvalAddHom x h
      (Finsupp.mapDomain
        (blockProjectKey (colorCharge gauge) (weakCharge gauge))
        (Finsupp.mapDomain (fun e => (e, s.offset))
          (∑ i : (blockChargedWeightBasis s).ι,
            Finsupp.single ((blockChargedWeightBasis s).weight i) 1))) = _
  rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp [resolvedEvalAddHom, eval]

theorem blockChargedProductRho_character
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (blockChargedProductRho gauge s).character
        (Multiplicative.ofAdd x, h) =
      eval
        (blockResolved (colorCharge gauge) (weakCharge gauge)
          (rawResolvedWithOffset s.offset
            s.rep.ambientLaurentModel.poly)) x h := by
  calc
    (blockChargedProductRho gauge s).character
        (Multiplicative.ofAdd x, h) =
      ∑ i : (blockChargedWeightBasis s).ι,
        keyMonoidHom
          (blockProjectKey (colorCharge gauge) (weakCharge gauge)
            ((blockChargedWeightBasis s).weight i, s.offset))
          (Multiplicative.ofAdd x, h) :=
        blockChargedProductRho_character_eq_weightSum gauge s x h
    _ = eval
        (blockResolved (colorCharge gauge) (weakCharge gauge)
          (rawResolvedWithOffset s.offset
            (blockChargedWeightBasis s).poly)) x h :=
      (eval_blockResolved_weightBasis gauge s x h).symm
    _ = eval
        (blockResolved (colorCharge gauge) (weakCharge gauge)
          (rawResolvedWithOffset s.offset
            s.rep.ambientLaurentModel.poly)) x h := by
      rw [blockChargedWeightBasis_poly]

theorem blockResolved_add
    {A : Type*} [AddCommGroup A]
    (color weak : A) (p q : RawResolvedCharacter A) :
    blockResolved color weak (p + q) =
      blockResolved color weak p + blockResolved color weak q := by
  exact Finsupp.mapDomain_add

theorem blockResolved_zsmul
    {A : Type*} [AddCommGroup A]
    (color weak : A) (n : ℤ) (p : RawResolvedCharacter A) :
    blockResolved color weak (n • p) =
      n • blockResolved color weak p := by
  exact Finsupp.mapDomain_smul
    (f := blockProjectKey color weak) n p

/-- The finite virtual product representation reconstructed from all external
character sectors with one common diagonal block lift. -/
def blockSourceProductRepresentation
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) :
    FiniteChargedContinuousUnitarySource (ChargeLabel H) →
      FiniteVirtualGroupRepresentation (CombinedGroup H)
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := blockChargedProductRepresentation gauge s } ::
        blockSourceProductRepresentation gauge source

theorem blockSourceProductRepresentation_character
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (blockSourceProductRepresentation gauge source)
        (Multiplicative.ofAdd x, h) =
      eval
        (blockResolved (colorCharge gauge) (weakCharge gauge)
          (rawResolvedSource source)) x h := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) *
            (blockChargedProductRho gauge s).character
              (Multiplicative.ofAdd x, h) +
            FiniteVirtualGroupRepresentation.character
              (blockSourceProductRepresentation gauge source)
              (Multiplicative.ofAdd x, h) =
          eval
            (blockResolved (colorCharge gauge) (weakCharge gauge)
              (s.coeff • rawResolvedWithOffset s.offset
                  s.rep.ambientLaurentModel.poly +
                rawResolvedSource source)) x h
      rw [blockResolved_add, blockResolved_zsmul,
        blockChargedProductRho_character, ih,
        eval_add, eval_zsmul]

/-!
## Transport from an actual conjugate block lift
-/

/-- Include only the residual factor in the physical-torus product group. -/
def residualInclusion
    {H : Type u} [CommGroup H] : H →* CombinedGroup H where
  toFun h := (1, h)
  map_one' := by
    ext <;> simp
  map_mul' h k := by
    ext <;> simp

@[simp]
theorem residualInclusion_apply
    {H : Type u} [CommGroup H] (h : H) :
    residualInclusion h = (1, h) := by
  rfl

theorem combinedBlockGaugeHom_residual
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) (h : H) :
    combinedBlockGaugeHom gauge (residualInclusion h) =
      AmbientTorus.toSU6MonoidHom (residualBlockAmbientHom gauge h) := by
  simp [combinedBlockGaugeHom, combinedBlockAmbientHom,
    residualInclusion]

/-- The residual representation on one charged sector using an actual
`SU(6)`-valued gauge lift. -/
def actualBlockChargedRho
    {H : Type u} [CommGroup H]
    (gauge : H →* ActualRestriction.SU6)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation ℂ H s.rep.V where
  toFun h :=
    LinearMap.lsmul ℂ s.rep.V (((s.offset.toMul h : Circle) : ℂ)) *
      s.rep.rho (gauge h)
  map_one' := by
    ext v
    simp
  map_mul' h k := by
    ext v
    simp only [map_mul]
    simp [smul_smul, mul_assoc]
    rw [mul_comm
      (((s.offset.toMul h : Circle) : ℂ))
      (((s.offset.toMul k : Circle) : ℂ))]

def actualBlockChargedRepresentation
    {H : Type u} [CommGroup H]
    (gauge : H →* ActualRestriction.SU6)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualGroupRepresentation H where
  V := s.rep.V
  rho := actualBlockChargedRho gauge s

/-- The standard diagonal block model restricted to its residual factor. -/
def diagonalBlockChargedRho
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation ℂ H s.rep.V :=
  (blockChargedProductRho gauge s).comp residualInclusion

/-- A group element acts as an invertible linear map in every
representation. -/
def representationElementLinearEquiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (g : G) : V ≃ₗ[ℂ] V where
  toLinearMap := rho g
  invFun := rho g⁻¹
  left_inv v := by
    change (rho g⁻¹ * rho g) v = v
    rw [← map_mul]
    simp
  right_inv v := by
    change (rho g * rho g⁻¹) v = v
    rw [← map_mul]
    simp

/-- The explicit geometric input still required from the semisimple embedding classification conjugacy
classification: one fixed `SU(6)` element simultaneously puts the supplied
centralizing gauge lift into the standard diagonal block torus. -/
structure ActualBlockDiagonalization
    (H : Type u) [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota) where
  conjugator : ActualRestriction.SU6
  gauge_eq : ∀ h,
    gauge h = conjugator *
      AmbientTorus.toSU6MonoidHom
        (residualBlockAmbientHom
          (actualBlockGaugeHom iota W gauge hCentral) h) *
      conjugator⁻¹

namespace ActualBlockDiagonalization

variable {H : Type u} [CommGroup H]
variable {iota : CompactEmbeddingClassification.ProductGroup →*
  CompactEmbeddingClassification.SU6}
variable {W : ActualBlockCentralizer.WeakDoubletData
  (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
variable {gauge : H →* CompactEmbeddingClassification.SU6}
variable {hCentral : ∀ h, gauge h ∈
  ActualCompactCentralizer.PhysicalCentralizer iota}

def blockGauge
    (_C : ActualBlockDiagonalization H iota W gauge hCentral) :
    H →* CompactBlockCentralizer.Group :=
  actualBlockGaugeHom iota W gauge hCentral

/-- Conjugation by the fixed standardizing element intertwines the diagonal
block-sector action with the actual gauge-sector action. -/
def chargedRepresentationEquiv
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation.Equiv
      (diagonalBlockChargedRho C.blockGauge s)
      (actualBlockChargedRho gauge s) where
  toLinearEquiv := representationElementLinearEquiv
    s.rep.rho C.conjugator
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply]
    change
      s.rep.rho C.conjugator
          (((s.offset.toMul h : Circle) : ℂ) •
            s.rep.rho
              (combinedBlockGaugeHom C.blockGauge (residualInclusion h)) v) =
        (((s.offset.toMul h : Circle) : ℂ) •
          s.rep.rho (gauge h) (s.rep.rho C.conjugator v))
    rw [map_smul, combinedBlockGaugeHom_residual]
    congr 1
    change
      (s.rep.rho C.conjugator *
          s.rep.rho
            (AmbientTorus.toSU6MonoidHom
              (residualBlockAmbientHom C.blockGauge h))) v =
        (s.rep.rho (gauge h) * s.rep.rho C.conjugator) v
    rw [← map_mul, ← map_mul, C.gauge_eq h]
    simp [blockGauge, mul_assoc]

theorem charged_character_eq
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) (h : H) :
    (actualBlockChargedRho gauge s).character h =
      eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedWithOffset s.offset
            s.rep.ambientLaurentModel.poly)) 0 h := by
  calc
    (actualBlockChargedRho gauge s).character h =
        (diagonalBlockChargedRho C.blockGauge s).character h := by
      exact (congrFun
        (Representation.char_iso (C.chargedRepresentationEquiv s)) h).symm
    _ = (blockChargedProductRho C.blockGauge s).character
        (Multiplicative.ofAdd (0 : UnitAddTorus (Fin 4)), h) := by
      change
        (blockChargedProductRho C.blockGauge s).character
            (residualInclusion h) = _
      rw [residualInclusion_apply]
      rfl
    _ = eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedWithOffset s.offset
            s.rep.ambientLaurentModel.poly)) 0 h :=
      blockChargedProductRho_character C.blockGauge s 0 h

/-- The finite virtual residual representation obtained by restoring the
actual common gauge lift on every external character sector. -/
def actualBlockSourceRepresentation
    (C : ActualBlockDiagonalization H iota W gauge hCentral) :
    FiniteChargedContinuousUnitarySource (ChargeLabel H) →
      FiniteVirtualGroupRepresentation H
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := actualBlockChargedRepresentation gauge s } ::
        C.actualBlockSourceRepresentation source

/-- The actual residual trace character of a finite charged source is the
raw block-resolved evaluator at the identity physical-torus point. -/
theorem source_character_eq
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (C.actualBlockSourceRepresentation source) h =
      eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedSource source)) 0 h := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) * (actualBlockChargedRho gauge s).character h +
            FiniteVirtualGroupRepresentation.character
              (C.actualBlockSourceRepresentation source) h =
          eval
            (blockResolved (colorCharge C.blockGauge)
              (weakCharge C.blockGauge)
              (s.coeff • rawResolvedWithOffset s.offset
                  s.rep.ambientLaurentModel.poly +
                rawResolvedSource source)) 0 h
      rw [blockResolved_add, blockResolved_zsmul,
        C.charged_character_eq, ih, eval_add, eval_zsmul]

theorem actualBlockSourceRepresentation_character_eq_list_sum
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (C.actualBlockSourceRepresentation source) h =
      (source.map fun s =>
        (s.coeff : ℂ) * (actualBlockChargedRho gauge s).character h).sum := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) * (actualBlockChargedRho gauge s).character h +
            FiniteVirtualGroupRepresentation.character
              (C.actualBlockSourceRepresentation source) h =
          (s.coeff : ℂ) * (actualBlockChargedRho gauge s).character h +
            (source.map fun t =>
              (t.coeff : ℂ) *
                (actualBlockChargedRho gauge t).character h).sum
      rw [ih]

end ActualBlockDiagonalization

/-!
## Agreement with each supplied physical character sector
-/

namespace CommonGaugeSummand

open FiniteResidualActionFactorization

variable {H : Type u} [CommGroup H]
variable {gauge : H →* CompactEmbeddingClassification.SU6}

/-- The charged summand associated with one full external character
eigenspace of a common-gauge physical source. -/
def indexedChargedSummand
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition)) :
    ChargedContinuousUnitarySummand (ChargeLabel H) where
  coeff := s.coeff
  rep := s.twisted.externalCommutingAction.characterSector
    (s.twisted.externalCommutingAction.indexedCharacter s.decomposition i)
  offset := Additive.ofMul
    (s.twisted.externalCommutingAction.indexedCharacter s.decomposition i)

/-- On every full external character sector, restoring the common actual
gauge lift gives exactly the originally supplied physical residual action. -/
theorem actualBlockChargedRho_apply_val
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition))
    (h : H) (v : (indexedChargedSummand s i).rep.V) :
    ((actualBlockChargedRho gauge (indexedChargedSummand s i) h v).1) =
      s.twisted.physical h v.1 := by
  let S := s.twisted.externalCommutingAction
  let chi := S.indexedCharacter s.decomposition i
  have hExternal : s.twisted.externalRepresentation h v.1 =
      ((chi h : Circle) : ℂ) • v.1 := v.2 h
  have hFactor := s.twisted.gauge_mul_external_apply h v.1
  have hGauge : s.twisted.gauge h = gauge h :=
    congrArg (fun f : H →* CompactEmbeddingClassification.SU6 => f h)
      s.gauge_eq
  change
    ((chi h : Circle) : ℂ) •
        (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.rho
          (StandardBlockGaugeCancellation.CommonGaugeSummand.rep s))
          (gauge h) v.1 = s.twisted.physical h v.1
  rw [← hGauge, ← hFactor, hExternal, map_smul]

theorem toChargedSource_eq_listOfFn_indexedChargedSummand
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge) :
    s.toChargedSource = List.ofFn fun i => indexedChargedSummand s i := by
  rfl

theorem physical_mapsTo_indexedCharacterSubmodule
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (h : H)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition)) :
    Set.MapsTo (s.twisted.physical h)
      (s.twisted.externalCommutingAction.indexedCharacterSubmodule
        s.decomposition i)
      (s.twisted.externalCommutingAction.indexedCharacterSubmodule
        s.decomposition i) := by
  intro v hv
  let vSector : (indexedChargedSummand s i).rep.V := ⟨v, hv⟩
  have hAction := actualBlockChargedRho_apply_val s i h vSector
  rw [← hAction]
  exact (actualBlockChargedRho gauge (indexedChargedSummand s i) h vSector).2

/-- The trace of the supplied physical action is the sum of the traces on
its full external character sectors. -/
theorem physical_character_eq_sum_indexedCharged
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (h : H) :
    s.twisted.physical.character h =
      ∑ i : Fin
          (s.twisted.externalCommutingAction.NumberOfActiveCharacters
            s.decomposition),
        (actualBlockChargedRho gauge
          (indexedChargedSummand s i)).character h := by
  unfold Representation.character
  rw [LinearMap.trace_eq_sum_trace_restrict
    (s.twisted.externalCommutingAction.indexedCharacterSubmodule_isInternal
      s.decomposition)
    (physical_mapsTo_indexedCharacterSubmodule s h)]
  apply Finset.sum_congr rfl
  intro i _hi
  have hRestrict :
      (s.twisted.physical h).restrict
          (physical_mapsTo_indexedCharacterSubmodule s h i) =
        actualBlockChargedRho gauge (indexedChargedSummand s i) h := by
    ext v
    exact (actualBlockChargedRho_apply_val s i h v).symm
  rw [hRestrict]
  rfl

theorem actualBlockSource_character_eq_coeff_mul_physical
    {iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6}
    {W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
    {hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota}
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (C.actualBlockSourceRepresentation s.toChargedSource) h =
      (s.coeff : ℂ) * s.twisted.physical.character h := by
  rw [C.actualBlockSourceRepresentation_character_eq_list_sum,
    toChargedSource_eq_listOfFn_indexedChargedSummand]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [physical_character_eq_sum_indexedCharged s h]
  simp only [indexedChargedSummand]
  rw [Finset.mul_sum]

end CommonGaugeSummand

namespace CommonGaugeSource

variable {H : Type u} [CommGroup H]
variable {gauge : H →* CompactEmbeddingClassification.SU6}

def physicalRepresentation
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge) :
    ActualGroupRepresentation H where
  V :=
    ContinuousUnitarySU6Representation.V
      (StandardBlockGaugeCancellation.CommonGaugeSummand.rep s)
  rho := s.twisted.physical

/-- The supplied physical residual representations, retaining their virtual
chiral coefficients. -/
def physicalVirtualRepresentation :
    StandardBlockGaugeCancellation.CommonGaugeSource H gauge →
      FiniteVirtualGroupRepresentation H
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := physicalRepresentation s } ::
        physicalVirtualRepresentation source

theorem rawResolvedSource_append
    {A : Type*}
    (source target :
      FiniteChargedContinuousUnitarySource A) :
    rawResolvedSource (source ++ target) =
      rawResolvedSource source + rawResolvedSource target := by
  induction source with
  | nil => simp [rawResolvedSource]
  | cons s source ih =>
      simp only [List.cons_append, rawResolvedSource]
      rw [ih]
      abel

theorem physicalSummand_character_eq_eval
    {iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6}
    {W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
    {hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota}
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (s : StandardBlockGaugeCancellation.CommonGaugeSummand H gauge)
    (h : H) :
    (s.coeff : ℂ) * s.twisted.physical.character h =
      eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedSource s.toChargedSource)) 0 h := by
  calc
    (s.coeff : ℂ) * s.twisted.physical.character h =
        FiniteVirtualGroupRepresentation.character
          (C.actualBlockSourceRepresentation s.toChargedSource) h :=
      (CommonGaugeSummand.actualBlockSource_character_eq_coeff_mul_physical
        C s h).symm
    _ = eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedSource s.toChargedSource)) 0 h :=
      C.source_character_eq s.toChargedSource h

/-- Conditional only on the explicit semisimple embedding classification standardizing conjugator, the
virtual trace of all supplied physical residual actions is exactly the raw
block-resolved character evaluator. -/
theorem physicalVirtualRepresentation_character_eq
    {iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6}
    {W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
    {hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota}
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (source : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (physicalVirtualRepresentation source) h =
      eval
        (blockResolved (colorCharge C.blockGauge) (weakCharge C.blockGauge)
          (rawResolvedSource
            (StandardBlockGaugeCancellation.CommonGaugeSource.toChargedSource
              source))) 0 h := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      simp only [physicalVirtualRepresentation,
        StandardBlockGaugeCancellation.CommonGaugeSource.toChargedSource,
        FiniteVirtualGroupRepresentation.character,
        VirtualGroupSummand.character]
      change
        (s.coeff : ℂ) * s.twisted.physical.character h +
            FiniteVirtualGroupRepresentation.character
              (physicalVirtualRepresentation source) h =
          eval
            (blockResolved (colorCharge C.blockGauge)
              (weakCharge C.blockGauge)
              (rawResolvedSource
                (s.toChargedSource ++
                  StandardBlockGaugeCancellation.CommonGaugeSource.toChargedSource
                    source))) 0 h
      rw [rawResolvedSource_append, blockResolved_add, eval_add,
        physicalSummand_character_eq_eval C s h, ih]

theorem physicalVirtualRepresentation_character_eq_actualBlockResolved
    {iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6}
    {W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
    {hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota}
    (C : ActualBlockDiagonalization H iota W gauge hCentral)
    (source : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (physicalVirtualRepresentation source) h =
      eval
        (actualBlockResolvedCharacter iota W gauge hCentral source) 0 h := by
  exact physicalVirtualRepresentation_character_eq C source h

end CommonGaugeSource

namespace OrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- The finite virtual residual representation carried by a strict ordinary
Abelian source.  The identity-lift conversion is definitionally the original
commuting physical action on every summand. -/
def physicalVirtualRepresentation
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H) :
    FiniteVirtualGroupRepresentation H :=
  CommonGaugeSource.physicalVirtualRepresentation
    source.toCommonGaugeSource

@[simp]
theorem convertedSummand_physical_rho
    (s : StandardBlockGaugeCancellation.OrdinaryAbelianSummand H) :
    (CommonGaugeSource.physicalRepresentation
      s.toCommonGaugeSummand).rho = s.action.rho :=
  rfl

/-- With a standardizing conjugator, the trace of the original strict
ordinary actions is exactly their charge-resolved finite-weight evaluator. -/
theorem physicalVirtualRepresentation_character_eq_ordinaryAbelianResolved
    {iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6}
    {W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota)}
    (C : ActualBlockDiagonalization H iota W
      (1 : H →* CompactEmbeddingClassification.SU6)
      (identityGauge_centralizes iota))
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (h : H) :
    FiniteVirtualGroupRepresentation.character
        (physicalVirtualRepresentation source) h =
      eval (ordinaryAbelianResolvedCharacter iota W source) 0 h :=
  CommonGaugeSource.physicalVirtualRepresentation_character_eq_actualBlockResolved
    C source.toCommonGaugeSource h

end OrdinaryAbelianSource

/-!
## Exact physical sources with an explicit semisimple embedding classification coordinate bridge
-/

/-- The raw block-projected exact-SM source together with the one remaining
geometric datum needed to interpret its evaluator as the supplied physical
trace: a fixed standardizing `SU(6)` conjugator. -/
structure PureSMActualBlockTraceSource
    (H : Type u) [CommGroup H] where
  toProjected : PureSMActualBlockProjectedSource H
  diagonalization : ActualBlockDiagonalization H
    toProjected.iota toProjected.weakDoubletData
    toProjected.gauge toProjected.gauge_centralizes

namespace PureSMActualBlockTraceSource

variable {H : Type u} [CommGroup H]

theorem physicalTrace_eq_blockResolved
    (S : PureSMActualBlockTraceSource H) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (CommonGaugeSource.physicalVirtualRepresentation
          S.toProjected.matter) h =
      eval
        (actualBlockResolvedCharacter S.toProjected.iota
          S.toProjected.weakDoubletData S.toProjected.gauge
          S.toProjected.gauge_centralizes S.toProjected.matter) 0 h :=
  CommonGaugeSource.physicalVirtualRepresentation_character_eq_actualBlockResolved
    S.diagonalization S.toProjected.matter h

/-- The local coefficient spectrum identifies the actual physical residual
trace with the canonical SM-plus-singlets target at every residual element. -/
theorem physicalTrace_eq_exactSMTarget
    (S : PureSMActualBlockTraceSource H) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (CommonGaugeSource.physicalVirtualRepresentation
          S.toProjected.matter) h =
      eval
        (exactSMWithSingletsResolvedCharacter
          S.toProjected.generations S.toProjected.physicalCharges
          S.toProjected.singlets) 0 h := by
  rw [S.physicalTrace_eq_blockResolved,
    S.toProjected.spectrum.resolvedCharacter_eq]

/-- The trace-interpreted source inherits the anomaly-independent standard charge-orbit bridge-to-Abelian proton-operator neutrality
proton-character conclusion. -/
theorem protonCharacters_eq_one
    (S : PureSMActualBlockTraceSource H) :
    protonFirstCharacter S.toProjected.physicalCharges = 1 ∧
      protonSecondCharacter S.toProjected.physicalCharges = 1 :=
  S.toProjected.protonCharacters_eq_one

theorem finiteAbelian_protonCharacters_eq_one
    [Finite H] (S : PureSMActualBlockTraceSource H) :
    protonFirstCharacter S.toProjected.physicalCharges = 1 ∧
      protonSecondCharacter S.toProjected.physicalCharges = 1 :=
  S.protonCharacters_eq_one

end PureSMActualBlockTraceSource

end
end StandardBlockPhysicalCharacterBridge
end GUT
