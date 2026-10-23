import GUT.SU6.Branching.StandardSMCharacterTarget
import Mathlib.Tactic

open Physics

open Math

/-!
# Actual standard-branch product characters

This file realizes the charge-resolved character constructed from a finite
continuous-unitary `SU(6)` source on the actual source vector spaces.  The
standard physical torus and the standard-central gauge lift both lie in the
ambient diagonal torus.  A source-sector residual character supplies the
remaining scalar action.  The trace of this product-group representation is
the faithful charge-resolved evaluator from `StandardSMCharacterTarget`.
-/

open scoped BigOperators

namespace GUT
namespace StandardPhysicalCharacterBridge

noncomputable section

open ContinuousUnitaryWeightDecomposition
open FiniteAbelianChargeSectors
open PhysicalRestrictionBridge
open StandardAbelianCharge
open StandardPhysicalSource
open StandardSMCharacterTarget

universe u

abbrev CompactTorus := StandardSMCharacterTarget.CompactTorus
abbrev CombinedGroup (H : Type u) :=
  StandardSMCharacterTarget.CombinedGroup H
abbrev ChargeLabel (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-- The common scalar `U(5)` circle, written in the five independent
coordinates of the ambient determinant-one torus. -/
def centralAmbientHom
    {H : Type u} [CommGroup H] (eta : H →* Circle) :
    H →* AmbientTorus.Torus where
  toFun h := fun _ => eta h
  map_one' := by
    funext i
    simp
  map_mul' h k := by
    funext i
    simp

theorem centralAmbientHom_eq_ofDiagonalPoint
    {H : Type u} [CommGroup H] (eta : H →* Circle) (h : H) :
    centralAmbientHom eta h =
      AmbientTorus.ofDiagonalPoint
        (StandardCentralGauge.diagonalPoint (eta h)) := by
  funext i
  apply Subtype.ext
  fin_cases i <;> rfl

theorem centralAmbientHom_toSU6
    {H : Type u} [CommGroup H] (eta : H →* Circle) (h : H) :
    AmbientTorus.toSU6MonoidHom (centralAmbientHom eta h) =
      StandardCentralGauge.hom (eta h) := by
  change
    (AmbientTorus.diagonalPoint (centralAmbientHom eta h)).toSU6 =
      StandardCentralGauge.hom (eta h)
  rw [centralAmbientHom_eq_ofDiagonalPoint,
    AmbientTorus.diagonalPoint_ofDiagonalPoint,
    StandardCentralGauge.diagonalPoint_toSU6_eq_hom]

/-- The standard physical torus and the standard-central lift combined in
the Abelian ambient torus. -/
def combinedAmbientHom
    {H : Type u} [CommGroup H] (eta : H →* Circle) :
    CombinedGroup H →* AmbientTorus.Torus :=
  (PhysicalSMTorusTarget.toAmbientTorus (-2) 3).coprod
    (centralAmbientHom eta)

/-- The corresponding actual gauge transformation in `SU(6)`. -/
def combinedGaugeHom
    {H : Type u} [CommGroup H] (eta : H →* Circle) :
    CombinedGroup H →* ActualRestriction.SU6 :=
  AmbientTorus.toSU6MonoidHom.comp (combinedAmbientHom eta)

@[simp]
theorem combinedGaugeHom_apply
    {H : Type u} [CommGroup H] (eta : H →* Circle)
    (x : CompactTorus) (h : H) :
    combinedGaugeHom eta (x, h) =
      PhysicalSMTorusTarget.embedding (-2) 3 x *
        StandardCentralGauge.hom (eta h) := by
  rw [combinedGaugeHom, combinedAmbientHom, MonoidHom.comp_apply,
    MonoidHom.coprod_apply, map_mul, centralAmbientHom_toSU6]
  rfl

/-- For the standard pair, normalizing an ambient weight removes precisely
the standard-central degree and leaves its physical `SU(5)` torus exponent. -/
theorem standardExponent_normalizeWeight
    (e : AmbientWeightLattice.Exponent) :
    standardExponent (normalizeWeight e) =
      PhysicalTorusCharacterBridge.restrictExponent (-2) 3 e := by
  ext i
  fin_cases i <;>
    simp [standardExponent, normalizeWeight,
      PhysicalTorusCharacterBridge.restrictExponent]
  all_goals ring

theorem exponent_eval_mul
    (e : AmbientWeightLattice.Exponent) (a b : AmbientTorus.Torus) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint (a * b)).toTorusVec =
      AmbientLaurent.Exponent.eval e
          (AmbientTorus.diagonalPoint a).toTorusVec *
        AmbientLaurent.Exponent.eval e
          (AmbientTorus.diagonalPoint b).toTorusVec := by
  simp only [AmbientTorus.exponent_eval_diagonalPoint, map_mul]
  rfl

theorem exponent_eval_physicalAmbient
    (e : AmbientWeightLattice.Exponent)
    (x : UnitAddTorus (Fin 4)) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (PhysicalSMTorusTarget.toAmbientTorus (-2) 3
            (Multiplicative.ofAdd x))).toTorusVec =
      UnitAddTorus.mFourier
        (PhysicalTorusCharacterBridge.restrictExponent (-2) 3 e) x := by
  rw [PhysicalSMTorusTarget.toAmbientTorus_eq_ofDiagonalPoint,
    AmbientTorus.diagonalPoint_ofDiagonalPoint]
  change
    AmbientLaurent.Exponent.eval e
        (AmbientLaurent.DiagonalPoint.ofUnitAddTorus
          (PhysicalTorusCharacterBridge.ambientTorusPoint (-2) 3 x)).toTorusVec =
      _
  rw [AmbientLaurent.DiagonalPoint.toTorusVec_ofUnitAddTorus,
    AmbientLaurent.Exponent.eval_torusVecOfUnitAddTorus,
    PhysicalTorusCharacterBridge.mFourier_ambientTorusPoint]

theorem exponent_eval_centralAmbient
    {H : Type u} [CommGroup H] (eta : H →* Circle)
    (e : AmbientWeightLattice.Exponent) (h : H) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (centralAmbientHom eta h)).toTorusVec =
      (((eta h) ^ StandardAbelianCharge.totalDegree e : Circle) : ℂ) := by
  rw [centralAmbientHom_eq_ofDiagonalPoint,
    AmbientTorus.diagonalPoint_ofDiagonalPoint,
    StandardCentralGauge.diagonalPoint_toTorusVec,
    StandardCentralGauge.exponent_eval_torusVec]

theorem exponent_eval_combinedAmbient
    {H : Type u} [CommGroup H] (eta : H →* Circle)
    (e : AmbientWeightLattice.Exponent)
    (x : UnitAddTorus (Fin 4)) (h : H) :
    AmbientLaurent.Exponent.eval e
        (AmbientTorus.diagonalPoint
          (combinedAmbientHom eta (Multiplicative.ofAdd x, h))).toTorusVec =
      UnitAddTorus.mFourier (standardExponent (normalizeWeight e)) x *
        (((eta h) ^ StandardAbelianCharge.totalDegree e : Circle) : ℂ) := by
  rw [combinedAmbientHom, MonoidHom.coprod_apply, exponent_eval_mul,
    exponent_eval_physicalAmbient, exponent_eval_centralAmbient,
    standardExponent_normalizeWeight]

/-- The reconstructed action on one charged source sector: the two gauge
torus factors act through the actual `SU(6)` representation, while the
sector offset acts by its scalar residual character. -/
def chargedProductRho
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    Representation ℂ (CombinedGroup H) s.rep.V where
  toFun g :=
    LinearMap.lsmul ℂ s.rep.V (((s.offset.toMul g.2 : Circle) : ℂ)) *
      s.rep.rho (combinedGaugeHom eta g)
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

def chargedProductRepresentation
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    ActualGroupRepresentation (CombinedGroup H) where
  V := s.rep.V
  rho := chargedProductRho eta s

/-- The canonical integral ambient-torus basis used to compute the actual
product character of a charged source sector. -/
def chargedWeightBasis
    {H : Type u} [CommGroup H]
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    IntegerWeightBasis s.rep.rho :=
  integerWeightBasisOfContinuousUnitary s.rep.rho
    s.rep.unitary s.rep.continuous_action

theorem chargedWeightBasis_poly
    {H : Type u} [CommGroup H]
    (s : ChargedContinuousUnitarySummand (ChargeLabel H)) :
    (chargedWeightBasis s).poly = s.rep.ambientLaurentModel.poly := by
  rfl

theorem chargedProductRho_action_on_weightBasis
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H)
    (i : (chargedWeightBasis s).ι) :
    chargedProductRho eta s (Multiplicative.ofAdd x, h)
        ((chargedWeightBasis s).basis i) =
      keyMonoidHom
          (affineProjectKey (centralDegreeCharge eta) s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) •
        (chargedWeightBasis s).basis i := by
  let B := chargedWeightBasis s
  have hBasis := B.action_on_basis
    (combinedAmbientHom eta (Multiplicative.ofAdd x, h)) i
  change
    s.rep.rho
        (combinedGaugeHom eta (Multiplicative.ofAdd x, h))
        (B.basis i) =
      AmbientLaurent.Exponent.eval (B.weight i)
          (AmbientTorus.diagonalPoint
            (combinedAmbientHom eta
              (Multiplicative.ofAdd x, h))).toTorusVec •
        B.basis i at hBasis
  change
    ((s.offset.toMul h : Circle) : ℂ) •
        s.rep.rho
          (combinedGaugeHom eta (Multiplicative.ofAdd x, h))
          (B.basis i) = _
  rw [hBasis, smul_smul, exponent_eval_combinedAmbient]
  change
    (((s.offset.toMul h : Circle) : ℂ) *
        (UnitAddTorus.mFourier
          (standardExponent (normalizeWeight (B.weight i))) x *
        (((eta h) ^ totalDegree (B.weight i) : Circle) : ℂ))) •
        B.basis i = _
  rw [keyMonoidHom_apply]
  change
    (((s.offset.toMul h : Circle) : ℂ) *
        (UnitAddTorus.mFourier
          (standardExponent (normalizeWeight (B.weight i))) x *
        (((eta h) ^ totalDegree (B.weight i) : Circle) : ℂ))) •
        B.basis i =
      (UnitAddTorus.mFourier
          (standardExponent (normalizeWeight (B.weight i))) x *
        ((((s.offset + centralDegreeCharge eta
          (totalDegree (B.weight i))).toMul h : Circle) : ℂ))) •
        B.basis i
  rw [chargeLabel_add_apply, centralDegreeCharge_toMul,
    MonoidHom.zpow_apply]
  congr 1
  ring

theorem chargedProductRho_character_eq_weightSum
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (chargedProductRho eta s).character (Multiplicative.ofAdd x, h) =
      ∑ i : (chargedWeightBasis s).ι,
        keyMonoidHom
          (affineProjectKey (centralDegreeCharge eta) s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) := by
  unfold Representation.character
  exact WeightTheory.trace_eq_sum_of_basis_eigen
    (chargedWeightBasis s).basis
    (chargedProductRho eta s (Multiplicative.ofAdd x, h))
    (fun i =>
      keyMonoidHom
        (affineProjectKey (centralDegreeCharge eta) s.offset
          ((chargedWeightBasis s).weight i))
        (Multiplicative.ofAdd x, h))
    (chargedProductRho_action_on_weightBasis eta s x h)

/-- Evaluation at a fixed product-group point is additive in the resolved
finite character. -/
def resolvedEvalAddHom
    {H : Type u} [CommGroup H]
    (x : UnitAddTorus (Fin 4)) (h : H) :
    StandardAbelianCharge.ResolvedCharacter (ChargeLabel H) →+ ℂ where
  toFun p := eval p x h
  map_zero' := by
    simp [eval]
  map_add' p q := by
    classical
    rw [eval, eval, eval, Finsupp.sum_add_index]
    · intro key _hkey
      simp
    · intro key _hkey a b
      rw [Int.cast_add]
      ring

@[simp]
theorem resolvedEvalAddHom_apply
    {H : Type u} [CommGroup H]
    (x : UnitAddTorus (Fin 4)) (h : H)
    (p : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H)) :
    resolvedEvalAddHom x h p = eval p x h :=
  rfl

theorem eval_chargeResolvedWeightBasis
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval
        (chargeResolvedWithOffset (centralDegreeCharge eta) s.offset
          (chargedWeightBasis s).poly) x h =
      ∑ i : (chargedWeightBasis s).ι,
        keyMonoidHom
          (affineProjectKey (centralDegreeCharge eta) s.offset
            ((chargedWeightBasis s).weight i))
          (Multiplicative.ofAdd x, h) := by
  change
    resolvedEvalAddHom x h
      (Finsupp.mapDomain
        (affineProjectKey (centralDegreeCharge eta) s.offset)
        (∑ i : (chargedWeightBasis s).ι,
          Finsupp.single ((chargedWeightBasis s).weight i) 1)) = _
  rw [Finsupp.mapDomain_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finsupp.mapDomain_single]
  simp [resolvedEvalAddHom, eval]

theorem chargedProductRho_character
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (s : ChargedContinuousUnitarySummand (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    (chargedProductRho eta s).character (Multiplicative.ofAdd x, h) =
      eval
        (chargeResolvedWithOffset (centralDegreeCharge eta) s.offset
          s.rep.ambientLaurentModel.poly) x h := by
  calc
    (chargedProductRho eta s).character (Multiplicative.ofAdd x, h) =
        ∑ i : (chargedWeightBasis s).ι,
          keyMonoidHom
            (affineProjectKey (centralDegreeCharge eta) s.offset
              ((chargedWeightBasis s).weight i))
            (Multiplicative.ofAdd x, h) :=
      chargedProductRho_character_eq_weightSum eta s x h
    _ = eval
          (chargeResolvedWithOffset (centralDegreeCharge eta) s.offset
            (chargedWeightBasis s).poly) x h :=
      (eval_chargeResolvedWeightBasis eta s x h).symm
    _ = eval
          (chargeResolvedWithOffset (centralDegreeCharge eta) s.offset
            s.rep.ambientLaurentModel.poly) x h := by
      rw [chargedWeightBasis_poly]

theorem eval_add
    {H : Type u} [CommGroup H]
    (p q : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (p + q) x h = eval p x h + eval q x h :=
  (resolvedEvalAddHom x h).map_add p q

theorem eval_zsmul
    {H : Type u} [CommGroup H]
    (n : ℤ) (p : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    eval (n • p) x h = (n : ℂ) * eval p x h := by
  change resolvedEvalAddHom x h (n • p) = _
  rw [map_zsmul, zsmul_eq_mul]
  rfl

/-- The actual finite virtual product-group representation reconstructed from
all charged source sectors. -/
def sourceProductRepresentation
    {H : Type u} [CommGroup H]
    (eta : H →* Circle) :
    FiniteChargedContinuousUnitarySource (ChargeLabel H) →
      FiniteVirtualGroupRepresentation (CombinedGroup H)
  | [] => []
  | s :: source =>
      { coeff := s.coeff
        rep := chargedProductRepresentation eta s } ::
        sourceProductRepresentation eta source

theorem sourceProductRepresentation_character
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H))
    (x : UnitAddTorus (Fin 4)) (h : H) :
    FiniteVirtualGroupRepresentation.character
        (sourceProductRepresentation eta source)
        (Multiplicative.ofAdd x, h) =
      eval (source.resolvedCharacter (centralDegreeCharge eta)) x h := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) *
            (chargedProductRho eta s).character
              (Multiplicative.ofAdd x, h) +
            FiniteVirtualGroupRepresentation.character
              (sourceProductRepresentation eta source)
              (Multiplicative.ofAdd x, h) =
          eval
            (s.coeff •
                chargeResolvedWithOffset (centralDegreeCharge eta) s.offset
                  s.rep.ambientLaurentModel.poly +
              FiniteChargedContinuousUnitarySource.resolvedCharacter
                source (centralDegreeCharge eta)) x h
      rw [chargedProductRho_character, ih, eval_add, eval_zsmul]

/-- The reconstructed actual source is a character model for the canonical
charge-resolved `Finsupp`; this field therefore need not be postulated. -/
theorem sourceProductRepresentation_isCharacterModel
    {H : Type u} [CommGroup H]
    (eta : H →* Circle)
    (source : FiniteChargedContinuousUnitarySource (ChargeLabel H)) :
    IsCharacterModel
      (sourceProductRepresentation eta source)
      (source.resolvedCharacter (centralDegreeCharge eta)) :=
  sourceProductRepresentation_character eta source

/-!
## Agreement with the supplied gauge-twisted physical action
-/

/-- The indexed charged sector appearing in the `List.ofFn` decomposition of
one certified gauge-twisted summand. -/
def indexedChargedSector
    {H : Type u} [CommGroup H] {eta : H →* Circle}
    (s : FiniteResidualActionFactorization.StandardCentralSummand H eta)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition)) :
    ChargedContinuousUnitarySummand (ChargeLabel H) where
  coeff := s.coeff
  rep := s.twisted.externalCommutingAction.characterSector
    (s.twisted.externalCommutingAction.indexedCharacter s.decomposition i)
  offset := Additive.ofMul
    (s.twisted.externalCommutingAction.indexedCharacter s.decomposition i)

theorem toChargedSource_eq_indexedChargedSector
    {H : Type u} [CommGroup H] {eta : H →* Circle}
    (s : FiniteResidualActionFactorization.StandardCentralSummand H eta) :
    s.toChargedSource = List.ofFn (indexedChargedSector s) := by
  rfl

/-- Inclusion of an indexed charged sector into its original physical source
space. -/
def indexedSectorCoe
    {H : Type u} [CommGroup H] {eta : H →* Circle}
    (s : FiniteResidualActionFactorization.StandardCentralSummand H eta)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition)) :
    (indexedChargedSector s i).rep.V →ₗ[ℂ] s.rep.V := by
  change
    s.twisted.externalCommutingAction.indexedCharacterSubmodule
        s.decomposition i →ₗ[ℂ] s.rep.V
  exact
    (s.twisted.externalCommutingAction.indexedCharacterSubmodule
      s.decomposition i).subtype

/-- On every full character sector, the reconstructed residual action is the
original physical action, as an equality in the ambient source space. -/
theorem chargedProductRho_residual_action_eq_physical
    {H : Type u} [CommGroup H] {eta : H →* Circle}
    (s : FiniteResidualActionFactorization.StandardCentralSummand H eta)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.decomposition))
    (h : H) (v : (indexedChargedSector s i).rep.V) :
    indexedSectorCoe s i
        (chargedProductRho eta (indexedChargedSector s i) (1, h) v) =
      s.twisted.physical h (indexedSectorCoe s i v) := by
  let S := s.twisted.externalCommutingAction
  let chi := S.indexedCharacter s.decomposition i
  have hExternal :
      s.twisted.externalRepresentation h (indexedSectorCoe s i v) =
        ((chi h : Circle) : ℂ) • indexedSectorCoe s i v :=
    v.property h
  have hFactor := congrArg
    (fun f : Module.End ℂ s.rep.V => f (indexedSectorCoe s i v))
    (s.certifiedAction.centralGauge_mul_external_eq_physical h)
  change
    ((chi h : Circle) : ℂ) •
        s.rep.rho (combinedGaugeHom eta (1, h))
          (indexedSectorCoe s i v) =
      s.twisted.physical h (indexedSectorCoe s i v)
  rw [combinedGaugeHom_apply]
  simp only [map_one, one_mul]
  calc
    ((chi h : Circle) : ℂ) •
        s.rep.rho (StandardCentralGauge.hom (eta h))
          (indexedSectorCoe s i v) =
      s.rep.rho (StandardCentralGauge.hom (eta h))
        (((chi h : Circle) : ℂ) • indexedSectorCoe s i v) := by
          rw [map_smul]
    _ = s.rep.rho (StandardCentralGauge.hom (eta h))
        (s.twisted.externalRepresentation h (indexedSectorCoe s i v)) := by
          rw [hExternal]
    _ = s.twisted.physical h (indexedSectorCoe s i v) := hFactor

/-!
## standard charge-orbit bridge source certificates with a derived character model
-/

/-- A charged continuous-unitary source whose actual reconstructed product
representation has the exact SM-plus-singlets character.  Unlike
`StandardSMCharacterTarget.PureSMCharacterSource`, no separate
`IsCharacterModel` witness is required. -/
structure PureSMChargedCharacterSource
    (H : Type u) [CommGroup H] where
  centralCharacter : H →* Circle
  matter : FiniteChargedContinuousUnitarySource (ChargeLabel H)
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  characterEquivalent : IsSMTargetCharacterEquivalent
    (sourceProductRepresentation centralCharacter matter)
    generations charges singlets

namespace PureSMChargedCharacterSource

variable {H : Type u} [CommGroup H]

def toPureSMCharacterSource (S : PureSMChargedCharacterSource H) :
    StandardSMCharacterTarget.PureSMCharacterSource H where
  matter := S.matter
  centralCharge := centralDegreeCharge S.centralCharacter
  combinedRepresentation :=
    sourceProductRepresentation S.centralCharacter S.matter
  characterModel := sourceProductRepresentation_isCharacterModel
    S.centralCharacter S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent := S.characterEquivalent

/-- Faithfulness upgrades the actual whole-character statement to equality in
the canonical charge-resolved `Finsupp` normal form. -/
theorem resolvedCharacter_eq_target (S : PureSMChargedCharacterSource H) :
    S.matter.resolvedCharacter (centralDegreeCharge S.centralCharacter) =
      exactSMWithSingletsResolvedCharacter
        S.generations S.charges S.singlets :=
  exactResolvedCharacter_of_characterEquivalent
    S.generations S.charges S.singlets
    (sourceProductRepresentation_isCharacterModel
      S.centralCharacter S.matter)
    S.characterEquivalent

theorem charge_equalities (S : PureSMChargedCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toPureSMCharacterSource.charge_equalities

theorem protonCharacters_eq_one (S : PureSMChargedCharacterSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toPureSMCharacterSource.protonCharacters_eq_one

theorem protonPhases_eq_one
    (S : PureSMChargedCharacterSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  S.toPureSMCharacterSource.protonPhases_eq_one h

end PureSMChargedCharacterSource

/-- The gauge-twisted standard-central source with only the actual target
character equivalence left as its low-energy spectrum input. -/
structure PureSMStandardPhysicalCharacterSource
    (H : Type u) [CommGroup H] where
  centralCharacter : H →* Circle
  matter : FiniteResidualActionFactorization.StandardCentralSource
    H centralCharacter
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  characterEquivalent : IsSMTargetCharacterEquivalent
    (sourceProductRepresentation centralCharacter matter.toChargedSource)
    generations charges singlets

namespace PureSMStandardPhysicalCharacterSource

variable {H : Type u} [CommGroup H]

def toChargedCharacterSource
    (S : PureSMStandardPhysicalCharacterSource H) :
    PureSMChargedCharacterSource H where
  centralCharacter := S.centralCharacter
  matter := S.matter.toChargedSource
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent := S.characterEquivalent

theorem charge_equalities
    (S : PureSMStandardPhysicalCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toChargedCharacterSource.charge_equalities

/-- The standard physical character route is standard charge-orbit bridge followed by Abelian proton-operator neutrality and uses no
continuous-anomaly premise. -/
theorem protonCharacters_eq_one
    (S : PureSMStandardPhysicalCharacterSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toChargedCharacterSource.protonCharacters_eq_one

theorem protonPhases_eq_one
    (S : PureSMStandardPhysicalCharacterSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  S.toChargedCharacterSource.protonPhases_eq_one h

end PureSMStandardPhysicalCharacterSource

/-- Continuous ordinary-Abelian specialization.  Its conclusion still uses
only standard charge-orbit bridge and Abelian proton-operator neutrality; the continuous-`U(1)` anomaly calculation is not a premise. -/
structure PureSMContinuousPhysicalCharacterSource
    (H : Type u) [CommGroup H] [TopologicalSpace H] where
  centralCharacter : H →ₜ* Circle
  matter : FiniteResidualActionFactorization.ContinuousStandardCentralSource
    H centralCharacter
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  characterEquivalent : IsSMTargetCharacterEquivalent
    (sourceProductRepresentation (centralCharacter : H →* Circle)
      matter.toChargedSource)
    generations charges singlets

namespace PureSMContinuousPhysicalCharacterSource

variable {H : Type u} [CommGroup H] [TopologicalSpace H]

def toStandardPhysicalCharacterSource
    (S : PureSMContinuousPhysicalCharacterSource H) :
    PureSMStandardPhysicalCharacterSource H where
  centralCharacter := (S.centralCharacter : H →* Circle)
  matter := S.matter.toStandardCentralSource
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  singlets := S.singlets
  characterEquivalent := S.characterEquivalent

theorem charge_equalities
    (S : PureSMContinuousPhysicalCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  S.toStandardPhysicalCharacterSource.charge_equalities

theorem protonCharacters_eq_one
    (S : PureSMContinuousPhysicalCharacterSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toStandardPhysicalCharacterSource.protonCharacters_eq_one

theorem protonPhases_eq_one
    (S : PureSMContinuousPhysicalCharacterSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  S.toStandardPhysicalCharacterSource.protonPhases_eq_one h

end PureSMContinuousPhysicalCharacterSource

/-- Explicit finite-Abelian specialization of the derived physical-character
source bridge. -/
abbrev PureSMFinitePhysicalCharacterSource
    (H : Type u) [CommGroup H] [Finite H] :=
  PureSMStandardPhysicalCharacterSource H

namespace PureSMFinitePhysicalCharacterSource

variable {H : Type u} [CommGroup H] [Finite H]

theorem charge_equalities
    (S : PureSMFinitePhysicalCharacterSource H) :
    S.charges.quark = S.charges.up ∧
      S.charges.quark = S.charges.electron ∧
      S.charges.down = S.charges.lepton :=
  PureSMStandardPhysicalCharacterSource.charge_equalities S

theorem protonCharacters_eq_one
    (S : PureSMFinitePhysicalCharacterSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  PureSMStandardPhysicalCharacterSource.protonCharacters_eq_one S

theorem protonPhases_eq_one
    (S : PureSMFinitePhysicalCharacterSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  PureSMStandardPhysicalCharacterSource.protonPhases_eq_one S h

end PureSMFinitePhysicalCharacterSource

end
end StandardPhysicalCharacterBridge
end GUT
