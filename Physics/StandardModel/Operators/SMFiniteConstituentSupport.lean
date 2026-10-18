import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.QLFiniteSupport
import Math.RepresentationTheory.Decomposition.FiniteConstituentSupport
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient

/-! Actual mixed-content support through a constructed finite irreducible sum.
The block-equivalence tests remain unevaluated. There is no Weyl premise,
closed numerical certificate or assumption of specieswise singlet support. -/
namespace GUT.SMFiniteConstituentSupport
set_option autoImplicit false
noncomputable section
open Math Representation FiniteSemisimpleDecomposition

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group :=
  borel SMCombinedCompactAction.Group
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

def weakInclusion : TauCeti.SU2 →* SMCombinedCompactAction.Group :=
  (MonoidHom.inl _ _).comp ((MonoidHom.inr _ _).comp (MonoidHom.inl _ _))

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev source := SMCombinedCompactContinuity.sourceModel flavor p

/-- The complete decomposition is constructed; it is not an extra input. -/
def decomposition : Decomposition (source flavor p) :=
  (exists_decomposition (source flavor p)
    (CompactIrreducibleQuotient.semisimple _
      (SMCombinedCompactContinuity.source_continuous flavor p))).some

theorem blocks_bounded : (decomposition flavor p).numberOfBlocks ≤
    Module.finrank ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) := by
  have h := FiniteConstituentSupport.numberOfBlocks_le (decomposition flavor p)
  exact h.trans_eq
    (ContinuousUnitaryConstructions.basisCopyRepresentationEquiv
      (SMCombinedCompactContinuity.sourceBasis flavor p)
      (SMCombinedCompactAction.source flavor p)).finrank_eq.symm

theorem boson_restrict (m : ℕ) (delta : ℤ) :
    (SMCombinedCompactContinuity.bosonModel (H := H) m delta).comp weakInclusion =
      (TauCeti.SU2.symPowerModel m).toRepresentation := by
  ext g x
  simp [SMCombinedCompactContinuity.bosonModel, weakInclusion,
    Representation.charTwist,
    SMHiggsConstituents.character, SMHiggsConstituents.hyperProjection,
    SMCombinedCompactAction.gaugeEmbedding, SMMixedCompactCoefficients.retained,
    SMCombinedCompactContinuity.weakProjection]

theorem boson_irreducible (m : ℕ) (delta : ℤ) :
    IsIrreducible (SMCombinedCompactContinuity.bosonModel (H := H) m delta) := by
  have hi : IsIrreducible
      ((SMCombinedCompactContinuity.bosonModel (H := H) m delta).comp weakInclusion) := by
    rw [boson_restrict]
    exact TauCeti.SU2.isIrreducible_symPowerModel m
  let := hi
  exact RepresentationTheory.isIrreducible_of_comp _ weakInclusion

/-- A finite test of equivalence of actual representations, not a computed Boolean. -/
def Matches (m : ℕ) (delta : ℤ) (i : Fin (decomposition flavor p).numberOfBlocks) : Prop :=
  Nonempty (Representation.Equiv ((decomposition flavor p).blockRepresentation i)
    (SMCombinedCompactContinuity.bosonModel (H := H) m delta).dual)

theorem local_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) ↔ ∃ i, Matches flavor p m delta i := by
  let := boson_irreducible (H := H) m delta
  exact (SelectionCriteria.allowed_equiv ((SMMixedCompactCoefficients.localEquiv flavor p m delta).trans
    (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta).symm)).trans
      (FiniteConstituentSupport.coefficient_iff (decomposition flavor p)
        (SMCombinedCompactContinuity.bosonModel (H := H) m delta))

theorem kernel_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (SMFullLocalKernel.Kernel flavor p m delta) ↔
      ∃ i, Matches flavor p m delta i :=
  (SelectionCriteria.allowed_equiv (SMFullLocalKernel.coefficientEquiv flavor p m delta)).symm.trans
    (local_allowed_iff flavor p m delta)

variable {k : ℕ} [NeZero k] (q l : ZMod k)

theorem ql_test_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l p m delta) ↔
      QLFiniteSupport.charge q l p = 0 ∧
        ∃ i, Matches (QLFiniteSupport.flavor q l) p m delta i :=
  (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr Iff.rfl (local_allowed_iff (QLFiniteSupport.flavor q l) p m delta))

theorem original_ql_iff (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          ∃ i, Matches (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d) i :=
  (QLFiniteSupport.original_allowed_iff q l p h d).trans
    (and_congr Iff.rfl (exists_congr (fun m => and_congr Iff.rfl
      (local_allowed_iff (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d)))))

theorem original_ql_forbidden (h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ¬ (QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          ∃ i, Matches (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d) i) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_ql_iff p q l h d]

end
end GUT.SMFiniteConstituentSupport
