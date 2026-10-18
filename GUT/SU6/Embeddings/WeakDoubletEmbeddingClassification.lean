import GUT.SU6.Adapters.CompactProductClassification
import GUT.SU6.Hypercharge.ContinuousCentralizer
import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import GUT.SU6.Embeddings.LowDimensionalIrreps
import Mathlib.Data.List.OfFn

open Math

/-!
# Finite constituent bridge for weak-doublet embedding classification

This file combines complete reducibility, finite direct-sum decomposition,
product irreducible factorization, and the low-dimensional highest-weight
arithmetic.  The result is an actual finite list of the nine allowed block
kinds whose dimensions add to six.
-/

namespace GUT
namespace WeakDoubletEmbeddingClassification

open CompactEmbeddingClassification CompactProductFactorization
open ContinuousRepresentationScope FiniteSemisimpleDecomposition
open LowDimensionalIrreps ProductFactorization
open scoped MonoidAlgebra

noncomputable section

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- The unitary property descends to every invariant subspace. -/
theorem subrepresentation_unitary
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (S : Subrepresentation tau) :
    IsUnitaryRepresentation S.toRepresentation := by
  intro g x y
  exact hUnitary g x y

/-- One irreducible constituent, together with its continuous color/weak
factorization and its low-dimensional semantic block label. -/
structure ClassifiedIrreducibleBlock
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (tau : Representation ℂ ProductGroup W) where
  factor : ContinuousFactorWitness tau
  kind : BlockKind
  color_dimension :
    Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau factor.S).toSubmodule ∈
      ({1, 3, 6} : Finset ℕ)
  weak_dimension_pos :
    0 < Module.finrank ℂ
      (MultiplicityRangeSpace tau
        (firstSubmoduleRepresentation tau factor.S) factor.u)
  dimension_product :
    Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau factor.S).toSubmodule *
      Module.finrank ℂ
        (MultiplicityRangeSpace tau
          (firstSubmoduleRepresentation tau factor.S) factor.u) =
      Module.finrank ℂ W
  kind_dimension : kind.dimension = Module.finrank ℂ W
  color_active : kind.ColorActive ↔
    Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau factor.S).toSubmodule ≠ 1
  weak_active : kind.WeakActive ↔
    Module.finrank ℂ
        (MultiplicityRangeSpace tau
          (firstSubmoduleRepresentation tau factor.S) factor.u) ≠ 1
  color_inactive_action : ¬ kind.ColorActive →
    ∀ g, tau (g, 1) = LinearMap.id
  weak_inactive_action : ¬ kind.WeakActive →
    ∀ h, tau (1, h) = LinearMap.id
  weak_center_action :
    multiplicityRangeRepresentation tau
        (firstSubmoduleRepresentation tau factor.S) factor.u su2CenterElement =
      ((-1 : ℂ) ^
          (Module.finrank ℂ
            (MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau factor.S) factor.u) - 1)) •
        (LinearMap.id :
          MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau factor.S) factor.u →ₗ[ℂ]
            MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau factor.S) factor.u)

/-- Bounded irreducible classification and product factorization assign an
allowed block kind to every continuous irreducible unitary constituent of
dimension at most six. -/
theorem exists_classifiedIrreducibleBlock_of_lowDimensionalTheory
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (T : SU2SU3LowDimensionalTheory.{u})
    (tau : Representation ℂ ProductGroup W)
    [Nontrivial W] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ W ≤ 6) :
    Nonempty (ClassifiedIrreducibleBlock tau) := by
  obtain ⟨F, hColor, hCenter⟩ :=
    exists_classified_continuousFactorWitness_of_dimension_le_six_of_lowDimensionalTheory
      T tau hUnitary hContinuous hDimension
  let WeakSpace := MultiplicityRangeSpace tau
    (firstSubmoduleRepresentation tau F.S) F.u
  let weakRho := multiplicityRangeRepresentation tau
    (firstSubmoduleRepresentation tau F.S) F.u
  let : FiniteDimensional ℂ WeakSpace := F.secondFactor.finiteDimensional
  let : Representation.IsIrreducible weakRho := F.secondFactor.irreducible
  let : IsSimpleModule ℂ[SU2] weakRho.asModule := inferInstance
  let : Nontrivial WeakSpace := IsSimpleModule.nontrivial ℂ[SU2] weakRho.asModule
  have hWeak : 0 < Module.finrank ℂ WeakSpace :=
    Module.finrank_pos_iff.mpr inferInstance
  have hProduct := F.dimension_mul tau
  obtain ⟨b, hbDim, hbColor, hbWeak⟩ :=
    exists_blockKind_of_factor_dimensions_le_six
      (Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule)
      (Module.finrank ℂ WeakSpace) (Module.finrank ℂ W)
      hColor hWeak hProduct hDimension
  have hColorInactive : ¬ b.ColorActive →
      ∀ g, tau (g, 1) = LinearMap.id := by
    intro hb g
    have hColorOne :
        Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule = 1 := by
      by_contra hne
      exact hb (hbColor.mpr hne)
    apply F.first_action_eq_id tau g
    exact T.su3_action_eq_id_of_finrank_eq_one
      (firstSubmoduleAsSubrepresentation tau F.S).toRepresentation
      F.firstFactor hColorOne g
  have hWeakInactive : ¬ b.WeakActive →
      ∀ h, tau (1, h) = LinearMap.id := by
    intro hb h
    have hWeakOne : Module.finrank ℂ WeakSpace = 1 := by
      by_contra hne
      exact hb (hbWeak.mpr hne)
    apply F.second_action_eq_id tau h
    exact T.su2_action_eq_id_of_finrank_eq_one weakRho
      F.secondFactor hWeakOne h
  exact ⟨
    { factor := F
      kind := b
      color_dimension := hColor
      weak_dimension_pos := hWeak
      dimension_product := hProduct
      kind_dimension := hbDim
      color_active := hbColor
      weak_active := hbWeak
      color_inactive_action := hColorInactive
      weak_inactive_action := hWeakInactive
      weak_center_action := hCenter }⟩

/-- Compatibility wrapper for the original full highest-weight interface. -/
theorem exists_classifiedIrreducibleBlock
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (T : SU2SU3HighestWeightTheory.{u})
    (tau : Representation ℂ ProductGroup W)
    [Nontrivial W] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ W ≤ 6) :
    Nonempty (ClassifiedIrreducibleBlock tau) :=
  exists_classifiedIrreducibleBlock_of_lowDimensionalTheory
    T.toLowDimensionalTheory tau hUnitary hContinuous hDimension

/-- A compact-real differential on the two factors of this particular
irreducible constituent is enough to classify it.  No global assertion about
all continuous `SU(2)` or `SU(3)` irreducibles is used. -/
theorem exists_classifiedIrreducibleBlock_of_realDifferentiableFactorWitness
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (tau : Representation ℂ ProductGroup W)
    [Nontrivial W] [Representation.IsIrreducible tau]
    (R : RealDifferentiableFactorWitness tau)
    (hDimension : Module.finrank ℂ W ≤ 6) :
    Nonempty (ClassifiedIrreducibleBlock tau) := by
  let F := R.factor
  have hColor := R.color_dimension_mem_of_le_six hDimension
  have hCenter := R.weak_center_action_eq_dimension_sign
  let WeakSpace := MultiplicityRangeSpace tau
    (firstSubmoduleRepresentation tau F.S) F.u
  let weakRho := multiplicityRangeRepresentation tau
    (firstSubmoduleRepresentation tau F.S) F.u
  let : FiniteDimensional ℂ WeakSpace := F.secondFactor.finiteDimensional
  let : Representation.IsIrreducible weakRho := F.secondFactor.irreducible
  let : IsSimpleModule ℂ[SU2] weakRho.asModule := inferInstance
  let : Nontrivial WeakSpace := IsSimpleModule.nontrivial ℂ[SU2] weakRho.asModule
  have hWeak : 0 < Module.finrank ℂ WeakSpace :=
    Module.finrank_pos_iff.mpr inferInstance
  have hProduct := F.dimension_mul tau
  obtain ⟨b, hbDim, hbColor, hbWeak⟩ :=
    exists_blockKind_of_factor_dimensions_le_six
      (Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule)
      (Module.finrank ℂ WeakSpace) (Module.finrank ℂ W)
      hColor hWeak hProduct hDimension
  have hColorInactive : ¬ b.ColorActive →
      ∀ g, tau (g, 1) = LinearMap.id := by
    intro hb g
    have hColorOne :
        Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule = 1 := by
      by_contra hne
      exact hb (hbColor.mpr hne)
    apply F.first_action_eq_id tau g
    exact R.color_action_eq_id_of_finrank_eq_one hColorOne g
  have hWeakInactive : ¬ b.WeakActive →
      ∀ h, tau (1, h) = LinearMap.id := by
    intro hb h
    have hWeakOne : Module.finrank ℂ WeakSpace = 1 := by
      by_contra hne
      exact hb (hbWeak.mpr hne)
    apply F.second_action_eq_id tau h
    exact R.weak_action_eq_id_of_finrank_eq_one hWeakOne h
  exact ⟨
    { factor := F
      kind := b
      color_dimension := hColor
      weak_dimension_pos := hWeak
      dimension_product := hProduct
      kind_dimension := hbDim
      color_active := hbColor
      weak_active := hbWeak
      color_inactive_action := hColorInactive
      weak_inactive_action := hWeakInactive
      weak_center_action := hCenter }⟩

/-- It is enough to differentiate the two ambient factor restrictions of the
irreducible product action: the local factor differentials are obtained by
restriction to the subspaces selected by product factorization. -/
theorem exists_classifiedIrreducibleBlock_of_realDifferentiableProductAction
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (tau : Representation ℂ ProductGroup W)
    [Nontrivial W] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (R : RealDifferentiableProductAction tau)
    (hDimension : Module.finrank ℂ W ≤ 6) :
    Nonempty (ClassifiedIrreducibleBlock tau) := by
  obtain ⟨F⟩ := exists_realDifferentiableFactorWitness tau
    hUnitary hContinuous R
  exact exists_classifiedIrreducibleBlock_of_realDifferentiableFactorWitness
    tau F hDimension

/-- Both block kinds occurring in the weak-triplet branch are trivial on the
nontrivial center of the weak `SU(2)` factor. -/
theorem ClassifiedIrreducibleBlock.weakCenter_action_eq_id_of_kind
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (tau : Representation ℂ ProductGroup W)
    [Nontrivial W] [Representation.IsIrreducible tau]
    (B : ClassifiedIrreducibleBlock tau)
    (hKind : B.kind = .color3 ∨ B.kind = .weak3) :
    tau weakCenterElement = LinearMap.id := by
  rcases hKind with hColor | hWeak
  · have hInactive : ¬ B.kind.WeakActive := by
      simp [hColor, BlockKind.WeakActive]
    simpa [weakCenterElement] using
      B.weak_inactive_action hInactive su2CenterElement
  · let WeakSpace := MultiplicityRangeSpace tau
        (firstSubmoduleRepresentation tau B.factor.S) B.factor.u
    have hColorOne :
        Module.finrank ℂ
            (firstSubmoduleAsSubrepresentation tau B.factor.S).toSubmodule = 1 := by
      by_contra hne
      have hActive : B.kind.ColorActive := B.color_active.mpr hne
      simp [hWeak, BlockKind.ColorActive] at hActive
    have hAmbientThree : Module.finrank ℂ W = 3 := by
      have h := B.kind_dimension
      simpa [hWeak, BlockKind.dimension] using h.symm
    have hWeakThree : Module.finrank ℂ WeakSpace = 3 := by
      have hProduct := B.dimension_product
      change
        Module.finrank ℂ
            (firstSubmoduleAsSubrepresentation tau B.factor.S).toSubmodule *
          Module.finrank ℂ WeakSpace = Module.finrank ℂ W at hProduct
      rw [hColorOne, one_mul, hAmbientThree] at hProduct
      exact hProduct
    apply B.factor.second_action_eq_id tau su2CenterElement
    rw [B.weak_center_action]
    rw [hWeakThree]
    norm_num

/-- A finite semisimple decomposition with every simple constituent upgraded
to a classified continuous product block. -/
structure ClassifiedDecomposition
    (tau : Representation ℂ ProductGroup E) where
  decomposition : Decomposition tau
  constituent : ∀ i : Fin decomposition.numberOfBlocks,
    ClassifiedIrreducibleBlock
      (decomposition.subrepresentation i).toRepresentation

/-- A finite semisimple decomposition in which only the actually occurring
color and weak factors carry compact-real differential certificates. -/
structure RealDifferentiableDecomposition
    (tau : Representation ℂ ProductGroup E) where
  decomposition : Decomposition tau
  factor : ∀ i : Fin decomposition.numberOfBlocks,
    RealDifferentiableFactorWitness
      (decomposition.subrepresentation i).toRepresentation

namespace RealDifferentiableDecomposition

variable {tau : Representation ℂ ProductGroup E}

/-- Classify every actual constituent using its local factor differentials. -/
def toClassifiedDecomposition
    (R : RealDifferentiableDecomposition tau)
    (hDimension : Module.finrank ℂ E = 6) :
    ClassifiedDecomposition tau where
  decomposition := R.decomposition
  constituent := fun i => by
    let tauI := (R.decomposition.subrepresentation i).toRepresentation
    letI : Representation.IsIrreducible tauI :=
      R.decomposition.subrepresentation_isIrreducible i
    letI : IsSimpleModule ℂ[ProductGroup] tauI.asModule := inferInstance
    letI : Nontrivial (R.decomposition.subrepresentation i).toSubmodule :=
      IsSimpleModule.nontrivial ℂ[ProductGroup] tauI.asModule
    exact Classical.choice
      (exists_classifiedIrreducibleBlock_of_realDifferentiableFactorWitness
        tauI (R.factor i)
        ((Submodule.finrank_le
          (R.decomposition.subrepresentation i).toSubmodule).trans_eq hDimension))

end RealDifferentiableDecomposition

/-- Ambient `SU(3)` and `SU(2)` differentials on a product representation
descend through a unitary semisimple decomposition and then through product
factorization.  Thus no constituent-specific differential data is required. -/
theorem exists_realDifferentiableDecomposition_of_realDifferentiableProductAction
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (R : RealDifferentiableProductAction tau) :
    Nonempty (RealDifferentiableDecomposition tau) := by
  have hSemisimple := isSemisimpleRepresentation_of_unitary tau hUnitary
  obtain ⟨D⟩ := exists_decomposition tau hSemisimple
  refine ⟨{ decomposition := D, factor := fun i => Classical.choice ?_ }⟩
  let tauI := (D.subrepresentation i).toRepresentation
  let : Representation.IsIrreducible tauI :=
    D.subrepresentation_isIrreducible i
  let : IsSimpleModule ℂ[ProductGroup] tauI.asModule := inferInstance
  let : Nontrivial (D.subrepresentation i).toSubmodule :=
    IsSimpleModule.nontrivial ℂ[ProductGroup] tauI.asModule
  exact exists_realDifferentiableFactorWitness tauI
    (subrepresentation_unitary tau hUnitary (D.subrepresentation i))
    (D.subrepresentation_jointlyContinuous i hContinuous)
    (R.restrictToSubrepresentation (D.subrepresentation i))

/-- The former global compact-real differential theory constructs the new
local certificate, showing that the localized interface loses no existing
proofs. -/
theorem exists_realDifferentiableDecomposition_of_realLieHomDerivativeTheory
    (T : SU2SU3RealLieHomDerivativeTheory.{u})
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau) :
    Nonempty (RealDifferentiableDecomposition tau) := by
  have hSemisimple := isSemisimpleRepresentation_of_unitary tau hUnitary
  obtain ⟨D⟩ := exists_decomposition tau hSemisimple
  refine ⟨{ decomposition := D, factor := fun i => Classical.choice ?_ }⟩
  let tauI := (D.subrepresentation i).toRepresentation
  let : Representation.IsIrreducible tauI :=
    D.subrepresentation_isIrreducible i
  let : IsSimpleModule ℂ[ProductGroup] tauI.asModule := inferInstance
  let : Nontrivial (D.subrepresentation i).toSubmodule :=
    IsSimpleModule.nontrivial ℂ[ProductGroup] tauI.asModule
  have hUnitaryI :=
    subrepresentation_unitary tau hUnitary (D.subrepresentation i)
  have hContinuousI := D.subrepresentation_jointlyContinuous i hContinuous
  obtain ⟨F⟩ := exists_continuousFactorWitness tauI hUnitaryI hContinuousI
  obtain ⟨colorDifferential⟩ := T.su3_realLieHomDerivative
    (firstSubmoduleAsSubrepresentation tauI F.S).toRepresentation F.firstFactor
  obtain ⟨weakDifferential⟩ := T.su2_realLieHomDerivative
    (multiplicityRangeRepresentation tauI
      (firstSubmoduleRepresentation tauI F.S) F.u) F.secondFactor
  exact ⟨
    { factor := F
      colorDifferential := colorDifferential
      weakDifferential := weakDifferential }⟩

/-- The block list extracted from a classified finite decomposition. -/
def ClassifiedDecomposition.blocks
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau) : List BlockKind :=
  List.ofFn fun i => (C.constituent i).kind

/-- A continuous finite-dimensional unitary semisimple product
representation of dimension six has a finite list of classified irreducible
blocks. -/
theorem exists_classifiedDecomposition_of_lowDimensionalTheory
    (T : SU2SU3LowDimensionalTheory.{u})
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E = 6) :
    Nonempty (ClassifiedDecomposition tau) := by
  have hSemisimple := isSemisimpleRepresentation_of_unitary tau hUnitary
  obtain ⟨D⟩ := exists_decomposition tau hSemisimple
  refine ⟨⟨D, fun i => Classical.choice ?_⟩⟩
  let tauI := (D.subrepresentation i).toRepresentation
  let : Representation.IsIrreducible tauI :=
    D.subrepresentation_isIrreducible i
  let : IsSimpleModule ℂ[ProductGroup] tauI.asModule := inferInstance
  let : Nontrivial (D.subrepresentation i).toSubmodule :=
    IsSimpleModule.nontrivial ℂ[ProductGroup] tauI.asModule
  exact exists_classifiedIrreducibleBlock_of_lowDimensionalTheory T tauI
    (subrepresentation_unitary tau hUnitary (D.subrepresentation i))
    (D.subrepresentation_jointlyContinuous i hContinuous)
    ((Submodule.finrank_le (D.subrepresentation i).toSubmodule).trans_eq hDimension)

/-- Compatibility wrapper for the original full highest-weight interface. -/
theorem exists_classifiedDecomposition
    (T : SU2SU3HighestWeightTheory.{u})
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E = 6) :
    Nonempty (ClassifiedDecomposition tau) :=
  exists_classifiedDecomposition_of_lowDimensionalTheory
    T.toLowDimensionalTheory tau hUnitary hContinuous hDimension

/-- The dimensions of the extracted semantic blocks add to six. -/
theorem ClassifiedDecomposition.blocks_dimension
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hDimension : Module.finrank ℂ E = 6) :
    (C.blocks.map BlockKind.dimension).sum = 6 := by
  simp only [ClassifiedDecomposition.blocks, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [show (∑ i, (C.constituent i).kind.dimension) =
      ∑ i, Module.finrank ℂ (C.decomposition.block i) by
    apply Finset.sum_congr rfl
    intro i _
    exact (C.constituent i).kind_dimension]
  exact (C.decomposition.sum_finrank).trans hDimension

theorem ClassifiedDecomposition.exists_color_active
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hNontrivial : ∃ g : SU3, tau (g, 1) ≠ LinearMap.id) :
    ∃ i, (C.constituent i).kind.ColorActive := by
  by_contra hNone
  push Not at hNone
  obtain ⟨g, hg⟩ := hNontrivial
  apply hg
  apply C.decomposition.action_eq_id_of_forall_block
  intro i
  exact (C.constituent i).color_inactive_action (hNone i) g

theorem ClassifiedDecomposition.exists_weak_active
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hNontrivial : ∃ h : SU2, tau (1, h) ≠ LinearMap.id) :
    ∃ i, (C.constituent i).kind.WeakActive := by
  by_contra hNone
  push Not at hNone
  obtain ⟨h, hh⟩ := hNontrivial
  apply hh
  apply C.decomposition.action_eq_id_of_forall_block
  intro i
  exact (C.constituent i).weak_inactive_action (hNone i) h

/-- Once the two factors are witnessed to act nontrivially on at least one
constituent, the extracted list is the exact six-dimensional block
certificate consumed by the arithmetic semisimple embedding classification classifier. -/
def ClassifiedDecomposition.toSixDimensionalBlockDecomposition
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hDimension : Module.finrank ℂ E = 6)
    (hColor : ∃ i, (C.constituent i).kind.ColorActive)
    (hWeak : ∃ i, (C.constituent i).kind.WeakActive) :
    SixDimensionalBlockDecomposition where
  blocks := C.blocks
  dimension := C.blocks_dimension hDimension
  color_nontrivial := by
    obtain ⟨i, hi⟩ := hColor
    exact ⟨(C.constituent i).kind, by simp [ClassifiedDecomposition.blocks], hi⟩
  weak_nontrivial := by
    obtain ⟨i, hi⟩ := hWeak
    exact ⟨(C.constituent i).kind, by simp [ClassifiedDecomposition.blocks], hi⟩

/-- A weak-doublet certificate which retains the actual irreducible
constituents, rather than forgetting them after extracting branch counts. -/
structure ClassifiedWeakDoubletDecomposition
    (tau : Representation ℂ ProductGroup E) where
  classified : ClassifiedDecomposition tau
  dimension : Module.finrank ℂ E = 6
  color_active : ∃ i, (classified.constituent i).kind.ColorActive
  weak_active : ∃ i, (classified.constituent i).kind.WeakActive
  isWeakDoublet :
    (classified.toSixDimensionalBlockDecomposition
      dimension color_active weak_active).toBranchCounts.IsWeakDoubletBlock

namespace ClassifiedWeakDoubletDecomposition

variable {tau : Representation ℂ ProductGroup E}

/-- The numerical certificate underlying a classified weak-doublet
decomposition. -/
def toSixDimensionalBlockDecomposition
    (W : ClassifiedWeakDoubletDecomposition tau) :
    SixDimensionalBlockDecomposition :=
  W.classified.toSixDimensionalBlockDecomposition
    W.dimension W.color_active W.weak_active

/-- The actual constituent labels are exactly the color triplet, weak
doublet, and singlet, independently of their order in the semisimple
decomposition. -/
theorem blocks_perm_color3_weak2_singlet
    (W : ClassifiedWeakDoubletDecomposition tau) :
    List.Perm W.classified.blocks [.color3, .weak2, .singlet] :=
  W.toSixDimensionalBlockDecomposition
    |>.blocks_perm_color3_weak2_singlet_of_isWeakDoubletBlock W.isWeakDoublet

/-- A weak-doublet classified decomposition has exactly three irreducible
constituents. -/
theorem numberOfBlocks_eq_three
    (W : ClassifiedWeakDoubletDecomposition tau) :
    W.classified.decomposition.numberOfBlocks = 3 := by
  have hLength := W.blocks_perm_color3_weak2_singlet.length_eq
  simpa [ClassifiedDecomposition.blocks] using hLength

/-- No two actual constituents in the weak-doublet decomposition have the
same semantic block label. -/
theorem constituent_kind_injective
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Function.Injective (fun i => (W.classified.constituent i).kind) := by
  have hNodup : W.classified.blocks.Nodup :=
    W.blocks_perm_color3_weak2_singlet.nodup_iff.mpr (by simp)
  simpa [ClassifiedDecomposition.blocks, List.nodup_ofFn] using hNodup

/-- Each of the three standard semantic labels occurs at a unique actual
constituent index. -/
theorem existsUnique_constituent_kind
    (W : ClassifiedWeakDoubletDecomposition tau)
    {b : BlockKind} (hb : b ∈ [.color3, .weak2, .singlet]) :
    ∃! i, (W.classified.constituent i).kind = b := by
  have hbBlocks : b ∈ W.classified.blocks :=
    W.blocks_perm_color3_weak2_singlet.mem_iff.mpr hb
  simp only [ClassifiedDecomposition.blocks, List.mem_ofFn] at hbBlocks
  obtain ⟨i, hi⟩ := hbBlocks
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact W.constituent_kind_injective (hj.trans hi.symm)

/-- The canonical index of the color-triplet constituent. -/
noncomputable def colorIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Fin W.classified.decomposition.numberOfBlocks :=
  Classical.choose (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .color3) (by simp)))

@[simp]
theorem colorIndex_kind
    (W : ClassifiedWeakDoubletDecomposition tau) :
    (W.classified.constituent W.colorIndex).kind = .color3 :=
  Classical.choose_spec (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .color3) (by simp)))

/-- The canonical index of the weak-doublet constituent. -/
noncomputable def weakIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Fin W.classified.decomposition.numberOfBlocks :=
  Classical.choose (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .weak2) (by simp)))

@[simp]
theorem weakIndex_kind
    (W : ClassifiedWeakDoubletDecomposition tau) :
    (W.classified.constituent W.weakIndex).kind = .weak2 :=
  Classical.choose_spec (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .weak2) (by simp)))

/-- The canonical index of the singlet constituent. -/
noncomputable def singletIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Fin W.classified.decomposition.numberOfBlocks :=
  Classical.choose (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .singlet) (by simp)))

@[simp]
theorem singletIndex_kind
    (W : ClassifiedWeakDoubletDecomposition tau) :
    (W.classified.constituent W.singletIndex).kind = .singlet :=
  Classical.choose_spec (ExistsUnique.exists
    (W.existsUnique_constituent_kind (b := .singlet) (by simp)))

theorem colorIndex_ne_weakIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    W.colorIndex ≠ W.weakIndex := by
  intro h
  have hKind := congrArg (fun i => (W.classified.constituent i).kind) h
  simp at hKind

theorem colorIndex_ne_singletIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    W.colorIndex ≠ W.singletIndex := by
  intro h
  have hKind := congrArg (fun i => (W.classified.constituent i).kind) h
  simp at hKind

theorem weakIndex_ne_singletIndex
    (W : ClassifiedWeakDoubletDecomposition tau) :
    W.weakIndex ≠ W.singletIndex := by
  intro h
  have hKind := congrArg (fun i => (W.classified.constituent i).kind) h
  simp at hKind

/-- Every actual constituent has one of the three standard weak-doublet
labels. -/
theorem constituent_kind_cases
    (W : ClassifiedWeakDoubletDecomposition tau)
    (i : Fin W.classified.decomposition.numberOfBlocks) :
    (W.classified.constituent i).kind = .color3 ∨
      (W.classified.constituent i).kind = .weak2 ∨
      (W.classified.constituent i).kind = .singlet := by
  apply W.toSixDimensionalBlockDecomposition
    |>.block_eq_color3_or_weak2_or_singlet_of_isWeakDoubletBlock W.isWeakDoublet
  change (W.classified.constituent i).kind ∈ W.classified.blocks
  simp [ClassifiedDecomposition.blocks]

/-- The three canonical indices exhaust the semisimple decomposition. -/
theorem constituent_index_cases
    (W : ClassifiedWeakDoubletDecomposition tau)
    (i : Fin W.classified.decomposition.numberOfBlocks) :
    i = W.colorIndex ∨ i = W.weakIndex ∨ i = W.singletIndex := by
  rcases W.constituent_kind_cases i with hColor | hWeak | hSinglet
  · exact Or.inl
      (W.constituent_kind_injective (hColor.trans W.colorIndex_kind.symm))
  · exact Or.inr (Or.inl
      (W.constituent_kind_injective (hWeak.trans W.weakIndex_kind.symm)))
  · exact Or.inr (Or.inr
      (W.constituent_kind_injective (hSinglet.trans W.singletIndex_kind.symm)))

@[simp]
theorem colorBlock_finrank
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Module.finrank ℂ
      (W.classified.decomposition.block W.colorIndex) = 3 := by
  calc
    Module.finrank ℂ (W.classified.decomposition.block W.colorIndex) =
        (W.classified.constituent W.colorIndex).kind.dimension :=
      (W.classified.constituent W.colorIndex).kind_dimension.symm
    _ = 3 := by simp [BlockKind.dimension]

@[simp]
theorem weakBlock_finrank
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Module.finrank ℂ
      (W.classified.decomposition.block W.weakIndex) = 2 := by
  calc
    Module.finrank ℂ (W.classified.decomposition.block W.weakIndex) =
        (W.classified.constituent W.weakIndex).kind.dimension :=
      (W.classified.constituent W.weakIndex).kind_dimension.symm
    _ = 2 := by simp [BlockKind.dimension]

@[simp]
theorem singletBlock_finrank
    (W : ClassifiedWeakDoubletDecomposition tau) :
    Module.finrank ℂ
      (W.classified.decomposition.block W.singletIndex) = 1 := by
  calc
    Module.finrank ℂ (W.classified.decomposition.block W.singletIndex) =
        (W.classified.constituent W.singletIndex).kind.dimension :=
      (W.classified.constituent W.singletIndex).kind_dimension.symm
    _ = 1 := by simp [BlockKind.dimension]

end ClassifiedWeakDoubletDecomposition

/-- The weak center acts trivially on the entire representation whenever its
classified constituent list has the weak-triplet branch shape. -/
theorem ClassifiedDecomposition.weakCenter_action_eq_id_of_isWeakTripletBlock
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hDimension : Module.finrank ℂ E = 6)
    (hColor : ∃ i, (C.constituent i).kind.ColorActive)
    (hWeak : ∃ i, (C.constituent i).kind.WeakActive)
    (hTriplet :
      SemisimpleEmbedding.SixDimensionalBranchCounts.IsWeakTripletBlock
        (C.toSixDimensionalBlockDecomposition hDimension hColor hWeak).toBranchCounts) :
    tau weakCenterElement = LinearMap.id := by
  apply C.decomposition.action_eq_id_of_forall_block
  intro i
  let tauI := (C.decomposition.subrepresentation i).toRepresentation
  let : Representation.IsIrreducible tauI :=
    C.decomposition.subrepresentation_isIrreducible i
  let : IsSimpleModule ℂ[ProductGroup] tauI.asModule := inferInstance
  let : Nontrivial (C.decomposition.subrepresentation i).toSubmodule :=
    IsSimpleModule.nontrivial ℂ[ProductGroup] tauI.asModule
  apply (C.constituent i).weakCenter_action_eq_id_of_kind tauI
  apply SixDimensionalBlockDecomposition.block_eq_color3_or_weak3_of_isWeakTripletBlock
    (C.toSixDimensionalBlockDecomposition hDimension hColor hWeak) hTriplet
  simp [ClassifiedDecomposition.toSixDimensionalBlockDecomposition,
    ClassifiedDecomposition.blocks]

/-- In the tensor-product branch the unique `(3,2)` constituent has dimension
six, so it is the whole ambient representation. -/
theorem ClassifiedDecomposition.irreducible_of_isTensorProductBranch
    {tau : Representation ℂ ProductGroup E}
    (C : ClassifiedDecomposition tau)
    (hDimension : Module.finrank ℂ E = 6)
    (hColor : ∃ i, (C.constituent i).kind.ColorActive)
    (hWeak : ∃ i, (C.constituent i).kind.WeakActive)
    (hTensor :
      SemisimpleEmbedding.SixDimensionalBranchCounts.IsTensorProductBranch
        (C.toSixDimensionalBlockDecomposition hDimension hColor hWeak).toBranchCounts) :
    Representation.IsIrreducible tau := by
  have hRawCount :
      (RawBranchCounts.ofList C.blocks).tensor32 = 1 := by
    simpa [ClassifiedDecomposition.toSixDimensionalBlockDecomposition,
      SixDimensionalBlockDecomposition.toBranchCounts] using hTensor.1
  have hCount : C.blocks.count .tensor32 = 1 := by
    rw [← RawBranchCounts.multiplicity_ofList]
    simpa [RawBranchCounts.multiplicity] using hRawCount
  have hMem : BlockKind.tensor32 ∈ C.blocks := by
    apply List.count_pos_iff.mp
    omega
  simp only [ClassifiedDecomposition.blocks, List.mem_ofFn] at hMem
  obtain ⟨i, hi⟩ := hMem
  apply C.decomposition.irreducible_of_block_finrank_eq i
  calc
    Module.finrank ℂ (C.decomposition.block i) =
        (C.constituent i).kind.dimension :=
      (C.constituent i).kind_dimension.symm
    _ = 6 := by simp [hi, BlockKind.dimension]
    _ = Module.finrank ℂ E := hDimension.symm

/-- Abstract semisimple embedding classification block-list theorem: the only remaining global input is the
highest-weight classification packaged by `SU2SU3HighestWeightTheory`. -/
theorem exists_sixDimensionalBlockDecomposition
    (T : SU2SU3HighestWeightTheory.{u})
    (tau : Representation ℂ ProductGroup E)
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E = 6)
    (hColor : ∃ g : SU3, tau (g, 1) ≠ LinearMap.id)
    (hWeak : ∃ h : SU2, tau (1, h) ≠ LinearMap.id) :
    Nonempty SixDimensionalBlockDecomposition := by
  obtain ⟨C⟩ := exists_classifiedDecomposition T tau
    hUnitary hContinuous hDimension
  exact ⟨C.toSixDimensionalBlockDecomposition hDimension
    (C.exists_color_active hColor) (C.exists_weak_active hWeak)⟩

/-!
## The restricted defining representation of an injective embedding
-/

open LowDimensionalConcreteIrreps

/-- Faithfulness of the defining matrix action transports injectivity of the
proposed group embedding to nontriviality of every nonidentity source
element's action. -/
theorem euclideanDefiningRestriction_action_ne_id
    (iota : ProductGroup →* SU6) (hInjective : Function.Injective iota)
    {p : ProductGroup} (hp : p ≠ 1) :
    euclideanDefiningRestriction iota p ≠ LinearMap.id := by
  intro hAction
  apply hp
  apply hInjective
  rw [map_one]
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  change euclideanDefiningRestriction iota p =
    Matrix.toEuclideanLin (1 : Matrix (Fin 6) (Fin 6) ℂ)
  rw [hAction]
  exact (Matrix.toLpLin_one 2).symm

/-- Irreducibility passes from the Euclidean norm model to the ordinary
function-space model used by the matrix centralizer theorem. -/
theorem definingRestriction_irreducible_of_euclidean
    (iota : ProductGroup →* SU6)
    (hIrreducible :
      Representation.IsIrreducible (euclideanDefiningRestriction iota)) :
    Representation.IsIrreducible (definingRestriction iota) := by
  let : Representation.IsIrreducible (euclideanDefiningRestriction iota) :=
    hIrreducible
  exact ProductFactorization.isIrreducible_of_equiv
    (euclideanDefiningRestrictionEquiv iota).symm

/-- Assuming the global `SU(2)`/`SU(3)` highest-weight theorem, every
continuous injective `SU(3) x SU(2) -> SU(6)` homomorphism yields the exact
finite block certificate used by the checked arithmetic classification. -/
theorem injectiveEmbedding_has_sixDimensionalBlockDecomposition
    (T : SU2SU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota) :
    Nonempty SixDimensionalBlockDecomposition := by
  apply exists_sixDimensionalBlockDecomposition T
    (euclideanDefiningRestriction (iota : ProductGroup →* SU6))
  · exact euclideanDefiningRestriction_unitary (iota : ProductGroup →* SU6)
  · exact euclideanDefiningRestriction_jointlyContinuous iota
  · simp [EuclideanRepSpace]
  · refine ⟨su3SignElement 0, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    intro h
    exact su3SignElement_zero_ne_one (congrArg Prod.fst h)
  · refine ⟨su2CenterElement, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    exact weakCenterElement_ne_one

/-- Injectivity eliminates the numerical `(3,1) + (1,3)` branch: every such
constituent is fixed by `(1,-I₂)`, contradicting faithfulness of the defining
matrix representation. -/
theorem injectiveEmbedding_has_tensorProduct_or_weakDoubletBranch
    (T : SU2SU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsTensorProductBranch ∨
        D.toBranchCounts.IsWeakDoubletBlock := by
  let tau := euclideanDefiningRestriction (iota : ProductGroup →* SU6)
  have hDimension : Module.finrank ℂ EuclideanRepSpace = 6 := by
    simp [EuclideanRepSpace]
  have hColorAction : ∃ g : SU3, tau (g, 1) ≠ LinearMap.id := by
    refine ⟨su3SignElement 0, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    intro h
    exact su3SignElement_zero_ne_one (congrArg Prod.fst h)
  have hWeakAction : ∃ h : SU2, tau (1, h) ≠ LinearMap.id := by
    refine ⟨su2CenterElement, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    exact weakCenterElement_ne_one
  obtain ⟨C⟩ := exists_classifiedDecomposition T tau
    (euclideanDefiningRestriction_unitary (iota : ProductGroup →* SU6))
    (euclideanDefiningRestriction_jointlyContinuous iota) hDimension
  have hColor := C.exists_color_active hColorAction
  have hWeak := C.exists_weak_active hWeakAction
  let D := C.toSixDimensionalBlockDecomposition hDimension hColor hWeak
  have hNotTriplet : ¬ D.toBranchCounts.IsWeakTripletBlock := by
    intro hTriplet
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective weakCenterElement_ne_one
    exact C.weakCenter_action_eq_id_of_isWeakTripletBlock
      hDimension hColor hWeak hTriplet
  refine ⟨D, ?_⟩
  rcases D.classify with hTensor | hDoublet | hTriplet
  · exact Or.inl hTensor
  · exact Or.inr hDoublet
  · exact (hNotTriplet hTriplet).elim

/-- The physical hypercharge hypotheses and the bounded classification
package produce a weak-doublet decomposition which still carries all of its
actual irreducible subrepresentations. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_lowDimensionalTheory
    (T : SU2SU3LowDimensionalTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    Nonempty (ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) := by
  let tau := euclideanDefiningRestriction (iota : ProductGroup →* SU6)
  have hDimension : Module.finrank ℂ EuclideanRepSpace = 6 := by
    simp [EuclideanRepSpace]
  have hColorAction : ∃ g : SU3, tau (g, 1) ≠ LinearMap.id := by
    refine ⟨su3SignElement 0, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    intro h
    exact su3SignElement_zero_ne_one (congrArg Prod.fst h)
  have hWeakAction : ∃ h : SU2, tau (1, h) ≠ LinearMap.id := by
    refine ⟨su2CenterElement, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    exact weakCenterElement_ne_one
  obtain ⟨C⟩ := exists_classifiedDecomposition_of_lowDimensionalTheory T tau
    (euclideanDefiningRestriction_unitary (iota : ProductGroup →* SU6))
    (euclideanDefiningRestriction_jointlyContinuous iota) hDimension
  have hColor := C.exists_color_active hColorAction
  have hWeak := C.exists_weak_active hWeakAction
  let D := C.toSixDimensionalBlockDecomposition hDimension hColor hWeak
  have hNotTriplet : ¬ D.toBranchCounts.IsWeakTripletBlock := by
    intro hTriplet
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective weakCenterElement_ne_one
    exact C.weakCenter_action_eq_id_of_isWeakTripletBlock
      hDimension hColor hWeak hTriplet
  have hNotTensor : ¬ D.toBranchCounts.IsTensorProductBranch := by
    intro hTensor
    have hEuclideanIrreducible : Representation.IsIrreducible tau :=
      C.irreducible_of_isTensorProductBranch
        hDimension hColor hWeak hTensor
    have hOrdinaryIrreducible :
        Representation.IsIrreducible
          (definingRestriction (iota : ProductGroup →* SU6)) :=
      definingRestriction_irreducible_of_euclidean
        (iota : ProductGroup →* SU6) hEuclideanIrreducible
    let : Representation.IsIrreducible
        (definingRestriction (iota : ProductGroup →* SU6)) :=
      hOrdinaryIrreducible
    apply hNontrivial
    exact ContinuousCentralizer.commutingCircle_eq_one
      (iota : ProductGroup →* SU6) Y hCommute
  have hDoublet :=
    D.toBranchCounts.isWeakDoubletBlock_of_not_tensorProduct_of_not_weakTriplet
      hNotTensor hNotTriplet
  refine ⟨{
    classified := C
    dimension := hDimension
    color_active := hColor
    weak_active := hWeak
    isWeakDoublet := ?_ }⟩
  simpa [D] using hDoublet

/-- The same classified semisimple embedding classification conclusion from compact-real differentials only
on the finitely many factor representations actually occurring in the chosen
defining-restriction decomposition. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableDecomposition
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealDifferentiableDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    Nonempty (ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) := by
  let tau := euclideanDefiningRestriction (iota : ProductGroup →* SU6)
  have hDimension : Module.finrank ℂ EuclideanRepSpace = 6 := by
    simp [EuclideanRepSpace]
  have hColorAction : ∃ g : SU3, tau (g, 1) ≠ LinearMap.id := by
    refine ⟨su3SignElement 0, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    intro h
    exact su3SignElement_zero_ne_one (congrArg Prod.fst h)
  have hWeakAction : ∃ h : SU2, tau (1, h) ≠ LinearMap.id := by
    refine ⟨su2CenterElement, ?_⟩
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective
    exact weakCenterElement_ne_one
  let C : ClassifiedDecomposition tau :=
    R.toClassifiedDecomposition hDimension
  have hColor := C.exists_color_active hColorAction
  have hWeak := C.exists_weak_active hWeakAction
  let D := C.toSixDimensionalBlockDecomposition hDimension hColor hWeak
  have hNotTriplet : ¬ D.toBranchCounts.IsWeakTripletBlock := by
    intro hTriplet
    apply euclideanDefiningRestriction_action_ne_id
      (iota : ProductGroup →* SU6) hInjective weakCenterElement_ne_one
    exact C.weakCenter_action_eq_id_of_isWeakTripletBlock
      hDimension hColor hWeak hTriplet
  have hNotTensor : ¬ D.toBranchCounts.IsTensorProductBranch := by
    intro hTensor
    have hEuclideanIrreducible : Representation.IsIrreducible tau :=
      C.irreducible_of_isTensorProductBranch
        hDimension hColor hWeak hTensor
    have hOrdinaryIrreducible :
        Representation.IsIrreducible
          (definingRestriction (iota : ProductGroup →* SU6)) :=
      definingRestriction_irreducible_of_euclidean
        (iota : ProductGroup →* SU6) hEuclideanIrreducible
    let : Representation.IsIrreducible
        (definingRestriction (iota : ProductGroup →* SU6)) :=
      hOrdinaryIrreducible
    apply hNontrivial
    exact ContinuousCentralizer.commutingCircle_eq_one
      (iota : ProductGroup →* SU6) Y hCommute
  have hDoublet :=
    D.toBranchCounts.isWeakDoubletBlock_of_not_tensorProduct_of_not_weakTriplet
      hNotTensor hNotTriplet
  refine ⟨{
    classified := C
    dimension := hDimension
    color_active := hColor
    weak_active := hWeak
    isWeakDoublet := ?_ }⟩
  simpa [D] using hDoublet

/-- The classified semisimple embedding classification conclusion from compact-real differentials only on the
two factor restrictions of the ambient six-dimensional defining action.
Semisimple constituents and their product factors inherit these
differentials canonically. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableProductAction
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealDifferentiableProductAction
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    Nonempty (ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) := by
  let tau := euclideanDefiningRestriction (iota : ProductGroup →* SU6)
  obtain ⟨D⟩ :=
    exists_realDifferentiableDecomposition_of_realDifferentiableProductAction
      tau (euclideanDefiningRestriction_unitary (iota : ProductGroup →* SU6))
      (euclideanDefiningRestriction_jointlyContinuous iota) R
  exact
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableDecomposition
      iota hInjective Y hCommute hNontrivial D

/-- The classified semisimple embedding classification conclusion needs only real-linear identity
differentials whose values are verified on every one-parameter subgroup.
Their Lie laws are consequences of the representation identity. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realLinearlyDifferentiableProductAction
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealLinearlyDifferentiableProductAction
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    Nonempty (ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :=
  injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableProductAction
    iota hInjective Y hCommute hNontrivial
      R.toRealDifferentiableProductAction

/-- Compatibility wrapper for the original full highest-weight interface. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition
    (T : SU2SU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    Nonempty (ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :=
  injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- Under the physical requirement of a nontrivial continuous hypercharge
circle commuting with the semisimple image, injectivity and highest-weight
classification force the standard `(3,1) + (1,2) + (1,1)` branch.  This is
the numerical projection of the classified theorem above. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch
    (T : SU2SU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock := by
  obtain ⟨W⟩ :=
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition
      T iota hInjective Y hCommute hNontrivial
  exact ⟨W.toSixDimensionalBlockDecomposition, W.isWeakDoublet⟩

/-- The same semisimple embedding classification conclusion from precisely the bounded irreducible output
used in the six-dimensional argument. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    (T : SU2SU3LowDimensionalTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock := by
  obtain ⟨W⟩ :=
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_lowDimensionalTheory
      T iota hInjective Y hCommute hNontrivial
  exact ⟨W.toSixDimensionalBlockDecomposition, W.isWeakDoublet⟩

/-- Numerical semisimple embedding classification branch conclusion from the localized compact-real
differential certificate on the actual defining-restriction constituents. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realDifferentiableDecomposition
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealDifferentiableDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock := by
  obtain ⟨W⟩ :=
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableDecomposition
      iota hInjective Y hCommute hNontrivial R
  exact ⟨W.toSixDimensionalBlockDecomposition, W.isWeakDoublet⟩

/-- Numerical semisimple embedding classification branch conclusion from compact-real differentials on the
ambient color and weak restrictions of the defining representation. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realDifferentiableProductAction
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealDifferentiableProductAction
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock := by
  obtain ⟨W⟩ :=
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realDifferentiableProductAction
      iota hInjective Y hCommute hNontrivial R
  exact ⟨W.toSixDimensionalBlockDecomposition, W.isWeakDoublet⟩

/-- Numerical semisimple embedding classification branch conclusion from real-linear ambient differentials and
their actual one-parameter derivative identities. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realLinearlyDifferentiableProductAction
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (R : RealLinearlyDifferentiableProductAction
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realDifferentiableProductAction
    iota hInjective Y hCommute hNontrivial
      R.toRealDifferentiableProductAction

/-- The same semisimple embedding classification conclusion through the sharper interface whose `SU(2)`
dimension formula is supplied by the checked irreducible `sl₂` theorem. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lieTheory
    (T : SU2LieSU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch
    T.toSU2SU3HighestWeightTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem through fixed standard `sl₂(ℂ)` and `sl₃(ℂ)`
models.  The complete low-dimensional Lie-algebra classification is checked;
constructing `T` is exactly the remaining analytic group-to-Lie bridge. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_standardLieTheory
    (T : SU2SU3StandardLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The same semisimple embedding classification conclusion from the narrower integrated-Lie interface.  Lie
irreducibility is derived from group irreducibility and stability of Lie
submodules, rather than supplied as an independent certificate field. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_integratedLieTheory
    (T : SU2SU3IntegratedLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem from differentiated actions compatible with a
finite-product family of exponential generators.  Stability of Lie submodules
and zero-differential triviality are both derived internally. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_exponentialLieTheory
    (T : SU2SU3ExponentialLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem with the `SU(2)` center action derived from the
distinguished `pi * I * H` exponential generator. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_generatedExponentialLieTheory
    (T : SU2SU3GeneratedExponentialLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem from the concrete compact matrix exponential.  The
only source inputs left in `T` are surjectivity of that exponential and the
differentiation/exponential compatibility of each intended irreducible
representation. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_compactExponentialLieTheory
    (T : SU2SU3CompactExponentialLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem after finite-product generation of `SU(2)` and
`SU(3)` by compact exponentials has been proved internally.  The sole
remaining source certificate is differentiation of each intended continuous
irreducible representation together with `rho(exp X) = exp(d rho X)`. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_differentiatedExponentialLieTheory
    (T : SU2SU3DifferentiatedExponentialLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem from derivatives at the identity of the actual
`SU(2)` and `SU(3)` one-parameter actions.  Exponential compatibility and
compact exponential generation are both proved internally. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_derivativeAtIdentityLieTheory
    (T : SU2SU3DerivativeAtIdentityLieTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem from intrinsic complex Lie-algebra differentials of
the intended smooth `SU(2)` and `SU(3)` representations.  The Lie-module
structures and all global exponential consequences are derived internally. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lieHomDerivativeTheory
    (T : SU2SU3LieHomDerivativeTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

/-- The semisimple embedding classification branch theorem from the compact-real Lie differentials naturally
produced by differentiating the intended smooth `SU(2)` and `SU(3)`
representations.  Their complexification and all subsequent integration and
highest-weight steps are proved internally. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realLieHomDerivativeTheory
    (T : SU2SU3RealLieHomDerivativeTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ D : SixDimensionalBlockDecomposition,
      D.toBranchCounts.IsWeakDoubletBlock :=
  injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_lowDimensionalTheory
    T.toLowDimensionalTheory iota hInjective Y hCommute hNontrivial

end

end WeakDoubletEmbeddingClassification
end GUT
