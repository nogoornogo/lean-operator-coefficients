import GUT.SU6.Embeddings.WeakDoubletEmbeddingClassification
import GUT.SU6.Hypercharge.BlockCentralizer

open Math

/-!
# The hypercharge centralizer geometry commutant on the actual semisimple embedding classification constituents

This file orders the three actual irreducible constituents retained by the semisimple embedding classification
weak-doublet theorem.  Evaluation at their unique semantic indices identifies
the dependent direct sum with a `3+2+1` product representation.  The generic
Schur theorem in `BlockCentralizer` can then be applied without identifying the
constituents with separately chosen concrete models.
-/

namespace GUT
namespace ActualBlockCentralizer

open WeakDoubletEmbeddingClassification
open WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
open CompactEmbeddingClassification
open FiniteSemisimpleDecomposition

noncomputable section

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable {tau : Representation ℂ ProductGroup E}

abbrev WeakDoubletData (tau : Representation ℂ ProductGroup E) :=
  ClassifiedWeakDoubletDecomposition tau

/-- The color-triplet constituent space selected by its unique semantic
label. -/
abbrev ColorBlockSpace (W : WeakDoubletData tau) :=
  W.classified.decomposition.block W.colorIndex

/-- The weak-doublet constituent space selected by its unique semantic
label. -/
abbrev WeakBlockSpace (W : WeakDoubletData tau) :=
  W.classified.decomposition.block W.weakIndex

/-- The singlet constituent space selected by its unique semantic label. -/
abbrev SingletBlockSpace (W : WeakDoubletData tau) :=
  W.classified.decomposition.block W.singletIndex

/-- The dependent direct-sum space supplied by semisimple decomposition. -/
abbrev DecomposedSpace (W : WeakDoubletData tau) :=
  Π₀ i : Fin W.classified.decomposition.numberOfBlocks,
    W.classified.decomposition.block i

/-- The same actual constituent spaces, now ordered as color, weak, and
singlet. -/
abbrev OrderedBlockSpace (W : WeakDoubletData tau) :=
  ColorBlockSpace W × (WeakBlockSpace W × SingletBlockSpace W)

instance colorBlockSpace_finiteDimensional (W : WeakDoubletData tau) :
    FiniteDimensional ℂ (ColorBlockSpace W) :=
  FiniteDimensional.of_injective
    ((W.classified.decomposition.block W.colorIndex).subtype.restrictScalars ℂ)
    (W.classified.decomposition.block W.colorIndex).subtype_injective

instance weakBlockSpace_finiteDimensional (W : WeakDoubletData tau) :
    FiniteDimensional ℂ (WeakBlockSpace W) :=
  FiniteDimensional.of_injective
    ((W.classified.decomposition.block W.weakIndex).subtype.restrictScalars ℂ)
    (W.classified.decomposition.block W.weakIndex).subtype_injective

instance singletBlockSpace_finiteDimensional (W : WeakDoubletData tau) :
    FiniteDimensional ℂ (SingletBlockSpace W) :=
  FiniteDimensional.of_injective
    ((W.classified.decomposition.block W.singletIndex).subtype.restrictScalars ℂ)
    (W.classified.decomposition.block W.singletIndex).subtype_injective

instance colorBlockSpace_nontrivial (W : WeakDoubletData tau) :
    Nontrivial (ColorBlockSpace W) :=
  Module.finrank_pos_iff.mp
    (show 0 < Module.finrank ℂ (ColorBlockSpace W) by
      simp [ColorBlockSpace])

instance weakBlockSpace_nontrivial (W : WeakDoubletData tau) :
    Nontrivial (WeakBlockSpace W) :=
  Module.finrank_pos_iff.mp
    (show 0 < Module.finrank ℂ (WeakBlockSpace W) by
      simp [WeakBlockSpace])

instance singletBlockSpace_nontrivial (W : WeakDoubletData tau) :
    Nontrivial (SingletBlockSpace W) :=
  Module.finrank_pos_iff.mp
    (show 0 < Module.finrank ℂ (SingletBlockSpace W) by
      simp [SingletBlockSpace])

def colorBlockRepresentation (W : WeakDoubletData tau) :
    Representation ℂ ProductGroup (ColorBlockSpace W) :=
  W.classified.decomposition.blockRepresentation W.colorIndex

def weakBlockRepresentation (W : WeakDoubletData tau) :
    Representation ℂ ProductGroup (WeakBlockSpace W) :=
  W.classified.decomposition.blockRepresentation W.weakIndex

def singletBlockRepresentation (W : WeakDoubletData tau) :
    Representation ℂ ProductGroup (SingletBlockSpace W) :=
  W.classified.decomposition.blockRepresentation W.singletIndex

/-- The ordered product representation on the actual semisimple embedding classification constituent
spaces. -/
def orderedBlockRepresentation (W : WeakDoubletData tau) :
    Representation ℂ ProductGroup (OrderedBlockSpace W) :=
  (colorBlockRepresentation W).prod
    ((weakBlockRepresentation W).prod (singletBlockRepresentation W))

instance colorBlockRepresentation_isIrreducible (W : WeakDoubletData tau) :
    Representation.IsIrreducible (colorBlockRepresentation W) :=
  W.classified.decomposition.blockRepresentation_isIrreducible W.colorIndex

instance weakBlockRepresentation_isIrreducible (W : WeakDoubletData tau) :
    Representation.IsIrreducible (weakBlockRepresentation W) :=
  W.classified.decomposition.blockRepresentation_isIrreducible W.weakIndex

instance singletBlockRepresentation_isIrreducible (W : WeakDoubletData tau) :
    Representation.IsIrreducible (singletBlockRepresentation W) :=
  W.classified.decomposition.blockRepresentation_isIrreducible W.singletIndex

/-- Evaluate a dependent direct-sum vector at the three uniquely labelled
constituent indices. -/
def orderedProjectionLinearMap (W : WeakDoubletData tau) :
    DecomposedSpace W →ₗ[ℂ] OrderedBlockSpace W where
  toFun f := (f W.colorIndex, (f W.weakIndex, f W.singletIndex))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem orderedProjectionLinearMap_apply (W : WeakDoubletData tau)
    (f : DecomposedSpace W) :
    orderedProjectionLinearMap W f =
      (f W.colorIndex, (f W.weakIndex, f W.singletIndex)) :=
  rfl

theorem orderedProjectionLinearMap_injective (W : WeakDoubletData tau) :
    Function.Injective (orderedProjectionLinearMap W) := by
  intro f g h
  apply DFinsupp.ext
  intro i
  rcases W.constituent_index_cases i with hColor | hWeak | hSinglet
  · subst i
    exact congrArg Prod.fst h
  · subst i
    exact congrArg (fun x => x.2.1) h
  · subst i
    exact congrArg (fun x => x.2.2) h

theorem orderedProjectionLinearMap_surjective (W : WeakDoubletData tau) :
    Function.Surjective (orderedProjectionLinearMap W) := by
  rintro ⟨xColor, xWeak, xSinglet⟩
  let f : DecomposedSpace W :=
    DFinsupp.single W.colorIndex xColor +
      DFinsupp.single W.weakIndex xWeak +
      DFinsupp.single W.singletIndex xSinglet
  refine ⟨f, ?_⟩
  change
    (f W.colorIndex, (f W.weakIndex, f W.singletIndex)) =
      (xColor, (xWeak, xSinglet))
  apply Prod.ext
  · simp [f, W.colorIndex_ne_weakIndex.symm,
      W.colorIndex_ne_singletIndex.symm]
  · apply Prod.ext
    · simp [f, W.colorIndex_ne_weakIndex,
        W.weakIndex_ne_singletIndex.symm]
    · simp [f, W.colorIndex_ne_singletIndex,
        W.weakIndex_ne_singletIndex]

/-- The dependent direct sum and ordered actual-block product are linearly
equivalent. -/
def decomposedLinearEquivOrderedBlocks (W : WeakDoubletData tau) :
    DecomposedSpace W ≃ₗ[ℂ] OrderedBlockSpace W :=
  LinearEquiv.ofBijective (orderedProjectionLinearMap W)
    ⟨orderedProjectionLinearMap_injective W,
      orderedProjectionLinearMap_surjective W⟩

/-- Evaluation at the three actual constituent indices intertwines the direct
sum action with the ordered product action. -/
def decomposedEquivOrderedBlocks (W : WeakDoubletData tau) :
    Representation.Equiv
      W.classified.decomposition.directSumRepresentation
      (orderedBlockRepresentation W) := by
  let f : Representation.IntertwiningMap
      W.classified.decomposition.directSumRepresentation
      (orderedBlockRepresentation W) :=
    { toLinearMap := orderedProjectionLinearMap W
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        rfl }
  exact Representation.IntertwiningMap.ofBijective f
    ⟨orderedProjectionLinearMap_injective W,
      orderedProjectionLinearMap_surjective W⟩

/-- The original representation is equivalent to the ordered product of the
three actual irreducible semisimple embedding classification constituents. -/
def representationEquivOrderedBlocks (W : WeakDoubletData tau) :
    Representation.Equiv tau (orderedBlockRepresentation W) :=
  W.classified.decomposition.representationEquivDirectSum.trans
    (decomposedEquivOrderedBlocks W)

/-- The generic Schur theorem applies directly to the three actual semisimple embedding classification
constituents. -/
theorem orderedBlock_commutant_is_blockScalar
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W)) :
    ∃ c w s : ℂ, ∀ xColor xWeak xSinglet,
      f (xColor, (xWeak, xSinglet)) =
        (c • xColor, (w • xWeak, s • xSinglet)) := by
  apply BlockCentralizer.threeBlock_commutant_is_blockScalar
    (colorBlockRepresentation W) (weakBlockRepresentation W)
      (singletBlockRepresentation W)
  · simp [ColorBlockSpace, WeakBlockSpace]
  · simp [ColorBlockSpace, SingletBlockSpace]
  · simp [WeakBlockSpace, SingletBlockSpace]

/-- Every commutant endomorphism of the original representation becomes
block-scalar after transport to its actual ordered semisimple embedding classification constituents. -/
theorem actual_commutant_is_blockScalar
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap tau tau) :
    ∃ c w s : ℂ, ∀ xColor xWeak xSinglet,
      BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
          (representationEquivOrderedBlocks W) f
          (xColor, (xWeak, xSinglet)) =
        (c • xColor, (w • xWeak, s • xSinglet)) :=
  orderedBlock_commutant_is_blockScalar W
    (BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
      (representationEquivOrderedBlocks W) f)

/-- Scalar multiplication by `c`, `w`, and `s` on the three actual ordered
constituents. -/
def orderedBlockScalarLinearMap (W : WeakDoubletData tau) (c w s : ℂ) :
    OrderedBlockSpace W →ₗ[ℂ] OrderedBlockSpace W :=
  LinearMap.prodMap (c • LinearMap.id)
    (LinearMap.prodMap (w • LinearMap.id) (s • LinearMap.id))

@[simp]
theorem orderedBlockScalarLinearMap_apply (W : WeakDoubletData tau)
    (c w s : ℂ) (xColor : ColorBlockSpace W) (xWeak : WeakBlockSpace W)
    (xSinglet : SingletBlockSpace W) :
    orderedBlockScalarLinearMap W c w s (xColor, (xWeak, xSinglet)) =
      (c • xColor, (w • xWeak, s • xSinglet)) := by
  simp [orderedBlockScalarLinearMap]

/-- Every scalar-on-blocks map commutes with the ordered actual-block
representation. -/
def orderedBlockScalarIntertwiner (W : WeakDoubletData tau) (c w s : ℂ) :
    Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W) where
  toLinearMap := orderedBlockScalarLinearMap W c w s
  isIntertwining' g := by
    apply LinearMap.ext
    rintro ⟨xColor, xWeak, xSinglet⟩
    simp [orderedBlockRepresentation, orderedBlockScalarLinearMap]

/-- The scalar coefficients on the three nonzero actual constituent spaces
are uniquely detected by the resulting intertwiner. -/
theorem orderedBlockScalarIntertwiner_eq_iff
    (W : WeakDoubletData tau) {c w s c' w' s' : ℂ} :
    orderedBlockScalarIntertwiner W c w s =
        orderedBlockScalarIntertwiner W c' w' s' ↔
      c = c' ∧ w = w' ∧ s = s' := by
  constructor
  · intro h
    have hcAll : ∀ x : ColorBlockSpace W, c • x = c' • x := by
      intro x
      have hx := congrArg
        (fun q : Representation.IntertwiningMap
            (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
          (q (x, (0, 0))).1) h
      simpa [orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap] using hx
    have hwAll : ∀ x : WeakBlockSpace W, w • x = w' • x := by
      intro x
      have hx := congrArg
        (fun q : Representation.IntertwiningMap
            (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
          (q (0, (x, 0))).2.1) h
      simpa [orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap] using hx
    have hsAll : ∀ x : SingletBlockSpace W, s • x = s' • x := by
      intro x
      have hx := congrArg
        (fun q : Representation.IntertwiningMap
            (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
          (q (0, (0, x))).2.2) h
      simpa [orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap] using hx
    exact ⟨FaithfulSMul.eq_of_smul_eq_smul hcAll,
      FaithfulSMul.eq_of_smul_eq_smul hwAll,
      FaithfulSMul.eq_of_smul_eq_smul hsAll⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Equality form of the actual ordered-block Schur theorem. -/
theorem orderedBlock_commutant_eq_blockScalarIntertwiner
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W)) :
    ∃ c w s : ℂ, f = orderedBlockScalarIntertwiner W c w s := by
  obtain ⟨c, w, s, h⟩ := orderedBlock_commutant_is_blockScalar W f
  refine ⟨c, w, s, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨xColor, xWeak, xSinglet⟩
  exact h xColor xWeak xSinglet

/-- The trace on the actual blocks depends only on their checked dimensions
`3`, `2`, and `1`. -/
theorem trace_orderedBlockScalarLinearMap (W : WeakDoubletData tau)
    (c w s : ℂ) :
    LinearMap.trace ℂ (OrderedBlockSpace W)
      (orderedBlockScalarLinearMap W c w s) = 3 * c + 2 * w + s := by
  rw [orderedBlockScalarLinearMap, LinearMap.trace_prodMap',
    LinearMap.trace_prodMap']
  simp [ColorBlockSpace, WeakBlockSpace, SingletBlockSpace]
  ring

/-- The determinant on the actual blocks uses their checked dimensions
`3`, `2`, and `1`. -/
theorem det_orderedBlockScalarLinearMap (W : WeakDoubletData tau)
    (c w s : ℂ) :
    LinearMap.det (orderedBlockScalarLinearMap W c w s) =
      c ^ 3 * w ^ 2 * s := by
  rw [orderedBlockScalarLinearMap, LinearMap.det_prodMap,
    LinearMap.det_prodMap]
  simp [ColorBlockSpace, WeakBlockSpace, SingletBlockSpace]
  ring

/-- A traceless commutant element on the original representation has actual
block coefficients satisfying the `3+2+1` trace equation. -/
theorem traceless_actual_commutant
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap tau tau)
    (hTrace : LinearMap.trace ℂ E f.toLinearMap = 0) :
    ∃ c w s : ℂ,
      BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
          (representationEquivOrderedBlocks W) f =
        orderedBlockScalarIntertwiner W c w s ∧
      3 * c + 2 * w + s = 0 := by
  let fOrdered :=
    BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
      (representationEquivOrderedBlocks W) f
  obtain ⟨c, w, s, hf⟩ :=
    orderedBlock_commutant_eq_blockScalarIntertwiner W fOrdered
  refine ⟨c, w, s, hf, ?_⟩
  have hOrderedTrace :
      LinearMap.trace ℂ (OrderedBlockSpace W) fOrdered.toLinearMap = 0 := by
    rw [BlockCentralizer.trace_transportCommutant]
    exact hTrace
  rw [hf] at hOrderedTrace
  simpa [orderedBlockScalarIntertwiner,
    trace_orderedBlockScalarLinearMap] using hOrderedTrace

/-- The `Y5` and `X` combination on the actual semisimple embedding classification constituent spaces. -/
def orderedExtraIntertwiner (W : WeakDoubletData tau) (a b : ℂ) :
    Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W) :=
  orderedBlockScalarIntertwiner W (-2 * a + b) (3 * a + b) (-5 * b)

/-- The two `Y5/X` coefficients are unique on the actual constituent spaces. -/
theorem orderedExtraIntertwiner_injective (W : WeakDoubletData tau) :
    Function.Injective
      (fun p : ℂ × ℂ => orderedExtraIntertwiner W p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have hCoefficients := (orderedBlockScalarIntertwiner_eq_iff W).mp h
  rcases hCoefficients with ⟨hc, hw, _⟩
  have ha5 : 5 * a = 5 * a' := by
    calc
      5 * a = (3 * a + b) - (-2 * a + b) := by ring
      _ = (3 * a' + b') - (-2 * a' + b') := by rw [hw, hc]
      _ = 5 * a' := by ring
  have ha : a = a' := by
    calc
      a = (1 / 5 : ℂ) * (5 * a) := by ring
      _ = (1 / 5 : ℂ) * (5 * a') := by rw [ha5]
      _ = a' := by ring
  have hb : b = b' := by
    calc
      b = (-2 * a + b) + 2 * a := by ring
      _ = (-2 * a' + b') + 2 * a' := by rw [hc, ha]
      _ = b' := by ring
  exact Prod.ext ha hb

theorem orderedExtraIntertwiner_trace_zero (W : WeakDoubletData tau)
    (a b : ℂ) :
    LinearMap.trace ℂ (OrderedBlockSpace W)
      (orderedExtraIntertwiner W a b).toLinearMap = 0 := by
  rw [orderedExtraIntertwiner, orderedBlockScalarIntertwiner,
    trace_orderedBlockScalarLinearMap]
  ring

/-- Every traceless original commutant element transports to a `Y5/X`
combination on its actual ordered semisimple embedding classification constituents. -/
theorem traceless_actual_commutant_eq_orderedExtra
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap tau tau)
    (hTrace : LinearMap.trace ℂ E f.toLinearMap = 0) :
    ∃ a b : ℂ,
      BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
          (representationEquivOrderedBlocks W) f =
        orderedExtraIntertwiner W a b := by
  obtain ⟨c, w, s, hf, hTraceless⟩ :=
    traceless_actual_commutant W f hTrace
  let a := (w - c) / 5
  let b := -s / 5
  have hc : -2 * a + b = c := by
    dsimp [a, b]
    calc
      -2 * ((w - c) / 5) + -s / 5 =
          c - (3 * c + 2 * w + s) / 5 := by ring
      _ = c := by rw [hTraceless]; simp
  have hw : 3 * a + b = w := by
    dsimp [a, b]
    calc
      3 * ((w - c) / 5) + -s / 5 =
          w - (3 * c + 2 * w + s) / 5 := by ring
      _ = w := by rw [hTraceless]; simp
  have hs : -5 * b = s := by
    dsimp [b]
    ring
  refine ⟨a, b, ?_⟩
  rw [hf, orderedExtraIntertwiner, hc, hw, hs]

/-- The transported traceless commutant has a unique pair of `Y5/X`
coefficients. -/
theorem traceless_actual_commutant_eq_orderedExtra_unique
    (W : WeakDoubletData tau)
    (f : Representation.IntertwiningMap tau tau)
    (hTrace : LinearMap.trace ℂ E f.toLinearMap = 0) :
    ∃! p : ℂ × ℂ,
      BlockCentralizer.transportCommutant tau (orderedBlockRepresentation W)
          (representationEquivOrderedBlocks W) f =
        orderedExtraIntertwiner W p.1 p.2 := by
  obtain ⟨a, b, h⟩ :=
    traceless_actual_commutant_eq_orderedExtra W f hTrace
  refine ⟨(a, b), h, ?_⟩
  rintro ⟨a', b'⟩ h'
  apply orderedExtraIntertwiner_injective W
  exact h'.symm.trans h

/-!
## The physical semisimple embedding classification-to-hypercharge centralizer geometry composition
-/

/-- For an injective embedding with a nontrivial commuting hypercharge circle,
every traceless element of the complex commutant has unique `Y5/X`
coefficients after passing to the actual ordered irreducible constituents. -/
theorem injectiveEmbedding_traceless_commutant_has_unique_Y5_X_coefficients
    (T : ContinuousRepresentationScope.SU2SU3HighestWeightTheory.{0})
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (f : Representation.IntertwiningMap
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6)))
    (hTrace : LinearMap.trace ℂ EuclideanRepSpace f.toLinearMap = 0) :
    ∃ W : ClassifiedWeakDoubletDecomposition
        (euclideanDefiningRestriction (iota : ProductGroup →* SU6)),
      ∃! p : ℂ × ℂ,
        BlockCentralizer.transportCommutant
            (euclideanDefiningRestriction (iota : ProductGroup →* SU6))
            (orderedBlockRepresentation W)
            (representationEquivOrderedBlocks W) f =
          orderedExtraIntertwiner W p.1 p.2 := by
  obtain ⟨W⟩ :=
    injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition
      T iota hInjective Y hCommute hNontrivial
  exact ⟨W, traceless_actual_commutant_eq_orderedExtra_unique W f hTrace⟩

end

end ActualBlockCentralizer
end GUT
