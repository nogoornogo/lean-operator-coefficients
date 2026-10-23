import GUT.SU6.Branching.ConcreteSU6PhysicalTarget
import GUT.SU6.SelectionRules.Models.DiracPhysicalModel
import GUT.SU6.Branching.ConcreteStandardGeometry

open Physics

open Math

/-!
# A concrete Dirac benchmark with neutral residual action

The signed source is `15 + bar6 - 6`. The benchmark below concerns the
chiral index; a zero mass sector is allowed and does not remove vectorlike
zero modes.
-/

namespace GUT.ConcreteDiracBenchmark

open CompactEmbeddingClassification ContinuousUnitaryWeightDecomposition
open StandardBlockGaugeCancellation FiniteAbelianChargeSectors
open PhysicalChargeResolvedBridge StandardPhysicalSource
open ConcreteSU6Representations ConcreteSU6PhysicalTarget
open FiniteSemisimpleDecomposition

noncomputable section

set_option autoImplicit false

abbrev AnalyticRepresentation :=
  ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation

variable {H : Type*} [CommGroup H]

def neutralAction (R : AnalyticRepresentation) : CommutingAction H R where
  rho := 1
  unitary := by intro h v w; rfl
  commutes := by intro h g; simp

def matter (H : Type*) [CommGroup H] : OrdinaryAbelianSource H :=
  [{ coeff := 1, rep := exteriorTwo, action := neutralAction exteriorTwo },
   { coeff := 1, rep := antifundamental, action := neutralAction antifundamental },
   { coeff := -1, rep := fundamental, action := neutralAction fundamental }]

theorem blockCharacter_eq_one_of_trivial
    {R : AnalyticRepresentation} (S : CommutingAction H R)
    (hS : S.rho = 1) (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :
    S.blockCharacter D i = 1 := by
  let : IsSimpleModule (MonoidAlgebra ℂ H) (D.block i) := D.simple i
  let : Nontrivial (D.block i) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) (D.block i)
  apply MonoidHom.ext
  intro h
  apply Subtype.ext
  change (S.blockCharacter D i h : ℂ) = 1
  apply FaithfulSMul.eq_of_smul_eq_smul (α := D.block i)
  intro v
  rw [one_smul, ← S.blockRepresentation_action_eq_character D i h v]
  apply (D.blockAmbientEquiv i).injective
  change (D.blockAmbientEquiv i).toIntertwiningMap (D.blockRepresentation i h v) = _
  rw [Representation.IntertwiningMap.isIntertwining]
  apply Subtype.ext
  change S.rho h _ = _
  simp only [hS]
  rfl

theorem chargedSectorSource_neutral
    {R : AnalyticRepresentation} (S : CommutingAction H R)
    (hS : S.rho = 1) (D : Decomposition S.rho) (c : ℤ) :
    ∀ s ∈ S.chargedSectorSource D c, s.offset = 0 := by
  intro s hs
  simp only [CommutingAction.chargedSectorSource, List.mem_ofFn] at hs
  obtain ⟨i, rfl⟩ := hs
  change Additive.ofMul (S.indexedCharacter D i) = 0
  apply Additive.toMul.injective
  change S.indexedCharacter D i = 1
  have hi := (S.activeCharacterEquiv D i).property
  simp only [CommutingAction.activeCharacters, Finset.mem_image] at hi
  obtain ⟨j, _, hj⟩ := hi
  exact hj.symm.trans (blockCharacter_eq_one_of_trivial S hS D j)

theorem ordinaryChargedSource_neutral :
    ∀ s ∈ ordinaryChargedSource (matter H), s.offset = 0 := by
  have hs (s : OrdinaryAbelianSummand H) (ha : s.action.rho = 1) :
      ∀ t ∈ s.toCommonGaugeSummand.toChargedSource, t.offset = 0 := by
    apply chargedSectorSource_neutral
    change s.toCommonGaugeSummand.twisted.externalRepresentation = 1
    rw [OrdinaryAbelianSummand.toCommonGaugeSummand_externalRepresentation, ha]
    rfl
  intro s hmem
  change s ∈ _ ++ (_ ++ (_ ++ [])) at hmem
  simp only [List.mem_append, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  all_goals exact hs _ rfl s h

theorem matter_restrictedCharacter (x : UnitAddTorus (Fin 4)) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        (ordinaryChargedSource (matter H)).toVirtual
        (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x) =
      PhysicalTorusCharacterBridge.eval PhysicalTorusCharacterBridge.integralSMCharacter x := by
  rw [ordinaryChargedSource_restrictedCharacter_eq]
  simpa [matter, OrdinaryAbelianSource.toFiniteVirtual,
    OrdinaryAbelianSummand.toVirtualSummand,
    ContinuousUnitarySU6Representation.toActualRepresentation,
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter,
    AmbientCharacterBridge.summandRestrictedCharacter,
    AmbientCharacterBridge.actualRestrictedCharacter,
    ActualRestriction.restrictedCharacter, sub_eq_add_neg, add_assoc]
    using signed_character_physical x

theorem matter_resolvedCharacter :
    ordinaryPhysicalResolvedCharacter (-2) 3 (matter H) =
      exactSMWithSingletsResolvedCharacter 1
        (uniformCharges (0 : ChargeLabel H)) 0 := by
  change sourcePhysicalResolvedCharacter (-2) 3 (ordinaryChargedSource (matter H)) = _
  rw [uniform_sourcePhysicalResolvedCharacter (-2) 3 0 _ ordinaryChargedSource_neutral]
  have hIntegral : PhysicalTorusCharacterBridge.restrictIntegralCharacter (-2) 3
      (ordinaryChargedSource (matter H)).ambientLaurentModel.poly =
      PhysicalTorusCharacterBridge.integralSMCharacter := by
    apply PhysicalTorusCharacterBridge.Fourier.eval_faithful
    intro x
    rw [PhysicalTorusCharacterBridge.eval_restrictIntegralCharacter_eq_diagonalEval,
      (ordinaryChargedSource (matter H)).ambientLaurentModel.evaluates_character]
    exact matter_restrictedCharacter x
  rw [hIntegral, mapDomain_integralSMCharacter]

open PhysicalMassSpectrumBridge DiracPhysicalModel EquivariantMassIndex
open UnitaryVirtualRealization

/-- A proved source character determines the index for every invariant mass map. -/
theorem mass_hasExactSMChiralIndex_of_resolvedCharacter (m n : ℤ)
    (hCharacter : ordinaryPhysicalResolvedCharacter m n (matter H) =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0)
    (f : Representation.IntertwiningMap
      (ordinaryPositiveRepresentation m n (matter H)).rho
      (ordinaryNegativeRepresentation m n (matter H)).rho) :
    HasExactSMChiralIndex f (ordinaryNegativeRepresentation m n (matter H)).unitary
      1 (uniformCharges 0) 0 := by
  intro g
  refine (lightIndex_characterEquivalent_ultravioletIndex f
    (ordinaryPositiveRepresentation m n (matter H)).unitary
    (ordinaryNegativeRepresentation m n (matter H)).unitary g).trans ?_
  refine (PhysicalChargedCharacterBridge.canonicalUltravioletIndex_characterEquivalent
    m n (ordinaryChargedSource (matter H)) g).trans ?_
  change PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
      (PhysicalChargedCharacterBridge.sourceProductRepresentation m n
        (ordinaryChargedSource (matter H))) (Multiplicative.ofAdd g.1.toAdd, g.2) =
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0))
      (Multiplicative.ofAdd g.1.toAdd, g.2)
  rw [PhysicalChargedCharacterBridge.sourceProductRepresentation_character,
    PhysicalChargeResolvedEvaluation.character_ofCharacter]
  exact congrArg (fun p => PhysicalChargeResolvedEvaluation.eval p g.1.toAdd g.2)
    hCharacter

/-- The standard source satisfies the index condition without a spectrum assumption. -/
theorem mass_hasExactSMChiralIndex
    (f : Representation.IntertwiningMap
      (ordinaryPositiveRepresentation (-2) 3 (matter H)).rho
      (ordinaryNegativeRepresentation (-2) 3 (matter H)).rho) :
    HasExactSMChiralIndex f (ordinaryNegativeRepresentation (-2) 3 (matter H)).unitary
      1 (uniformCharges 0) 0 :=
  mass_hasExactSMChiralIndex_of_resolvedCharacter (-2) 3 matter_resolvedCharacter f

/-- A complete one-generation model, with neutral residual action and zero
bare mass, Yukawa family, and vacuum. Vectorlike zero modes are allowed. -/
def model (H : Type*) [CommGroup H] : ContinuousDiracYukawaModel H where
  geometry := ConcreteStandardGeometry.geometry
  matter := matter H
  scalar := ActualUnitaryGroupRepresentation.zero
  generations := 1
  generations_ne := by norm_num
  physicalCharges := uniformCharges 0
  singlets := 0
  massSector := DiracYukawaMass.Sector.zero
  hasExactSMChiralIndex := by
    have hm : ConcreteStandardGeometry.geometry.hyperchargePair.1 = -2 :=
      congrArg Prod.fst ConcreteStandardGeometry.hyperchargePair_eq_standard
    have hn : ConcreteStandardGeometry.geometry.hyperchargePair.2 = 3 :=
      congrArg Prod.snd ConcreteStandardGeometry.hyperchargePair_eq_standard
    apply mass_hasExactSMChiralIndex_of_resolvedCharacter
      ConcreteStandardGeometry.geometry.hyperchargePair.1
      ConcreteStandardGeometry.geometry.hyperchargePair.2
    rw [hm, hn]
    exact matter_resolvedCharacter

theorem model_generations : (model H).generations = 1 := rfl

theorem model_massMap_eq_zero : (model H).massMap = 0 := by
  apply Representation.IntertwiningMap.ext
  change (DiracYukawaMass.Sector.zero :
    DiracYukawaMass.Sector (model H).scalar.rho
      (positiveRepresentation (model H).geometry (model H).matter).rho
      (negativeRepresentation (model H).geometry (model H).matter).rho).inducedMass = 0
  exact DiracYukawaMass.Sector.zero_inducedMass

/-- Non-vacuity of the full model interface, without a spectrum hypothesis. -/
theorem exists_one_generation_model (H : Type*) [CommGroup H] :
    ∃ M : ContinuousDiracYukawaModel H, M.generations = 1 :=
  ⟨model H, rfl⟩

/-- The scoped selection-rule theorem applies to the constructed benchmark. -/
theorem model_not_forbidsEverySupportedPhysicalDeltaBOneOperator :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (StandardBlockChargeProjection.ordinaryAbelianResolvedCharacter
        ((model H).geometry.iota : ProductGroup →* CompactEmbeddingClassification.SU6)
        (model H).geometry.weakDoubletData (model H).matter) :=
  (model H).not_forbidsEverySupportedPhysicalDeltaBOneOperator

end
end GUT.ConcreteDiracBenchmark
