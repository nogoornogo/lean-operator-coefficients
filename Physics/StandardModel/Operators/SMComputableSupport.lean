import Physics.StandardModel.Operators.SMComputableCharacter
import Physics.StandardModel.Operators.SMQLPatternRequests

/-! Actual support from executable weight terms, under the existing Weyl input. -/
namespace GUT.SMComputableSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMCompactTorus SMComputableCharacter ComputableWeightPolynomial

local instance compactMeasurable : MeasurableSpace SMCombinedCompactAction.Group :=
  borel SMCombinedCompactAction.Group
local instance compactBorel : BorelSpace SMCombinedCompactAction.Group := ⟨rfl⟩

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev model := SMCompactMultiplicity.model flavor p

theorem presents (m : ℕ) (delta : ℤ) : CompactWeylExtraction.Presents
    (model flavor p m delta) inclusion.toMonoidHom monomial
    (polynomial (SMIteratedContent.counts p) m delta) := by
  intro t
  exact (terms_evaluation flavor p m delta t).symm.trans
    (presentation_evaluate (fun w => monomial w t) (terms (SMIteratedContent.counts p) m delta)).symm

variable (m : ℕ) (delta : ℤ) (input : SMCompactMultiplicity.Input flavor p m delta)

include input in
theorem kernel_dimension_int : (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) : ℤ) =
    multiplicity (SMIteratedContent.counts p) m delta := by
  have h := SMWeylExtractionInput.kernel_dimension_int flavor p m delta (model flavor p m delta)
    inclusion.toMonoidHom monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial (SMIteratedContent.counts p) m delta) (presents flavor p m delta)
  exact h.trans (extraction_eq _ _ _)

include input in
theorem nonnegative : 0 ≤ multiplicity (SMIteratedContent.counts p) m delta := by
  rw [← kernel_dimension_int flavor p m delta input]
  exact Int.natCast_nonneg _

include input in
theorem kernel_dimension : Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) =
    (multiplicity (SMIteratedContent.counts p) m delta).toNat := by
  simpa only [Int.toNat_natCast] using congrArg Int.toNat (kernel_dimension_int flavor p m delta input)

include input in
theorem rank_formula : Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
    SMIteratedContent.columns p m - (multiplicity (SMIteratedContent.counts p) m delta).toNat := by
  have hn := SMIteratedContent.rank_add_nullity flavor p m delta
  have hk := kernel_dimension flavor p m delta input
  omega

include input in
theorem local_allowed_iff : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor p m delta)) ↔ 0 < multiplicity (SMIteratedContent.counts p) m delta := by
  have h := SMWeylExtractionInput.local_allowed_iff flavor p m delta (model flavor p m delta)
    inclusion.toMonoidHom monomial roots (SMCombinedCompactContinuity.coefficientEquiv flavor p m delta)
    (SMCombinedCompactContinuity.continuous_model flavor p m delta) input
    (polynomial (SMIteratedContent.counts p) m delta) (presents flavor p m delta)
  simpa only [extraction_eq] using h

end
end GUT.SMComputableSupport

namespace GUT.SMComputableQLSupport
set_option autoImplicit false
open Math Representation SelectionCriteria
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev Input (m : ℕ) (delta : ℤ) := SMQLCompactMultiplicity.Input q l p m delta
def test (m : ℕ) (delta : ℤ) : Bool :=
  decide (QLFiniteSupport.charge q l p = 0 ∧
    0 < SMComputableCharacter.multiplicity (SMIteratedContent.counts p) m delta)

noncomputable section
theorem test_allowed_iff (m : ℕ) (delta : ℤ) (input : Input q l p m delta) :
    Allowed (QLFiniteSupport.Test q l p m delta) ↔ test q l p m delta = true := by
  rw [test,decide_eq_true_eq]
  exact (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr Iff.rfl (SMComputableSupport.local_allowed_iff (QLFiniteSupport.flavor q l) p m delta input))

theorem original_allowed_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1), Input q l p m.val ((h : ℤ)-d)) :
    Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
        test q l p m.val ((h : ℤ)-d) = true := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  exact exists_congr (fun m => and_congr Iff.rfl (test_allowed_iff q l p m.val _ (input m)))

theorem original_forbidden_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1), Input q l p m.val ((h : ℤ)-d)) :
    Forbidden (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ∀ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val →
        test q l p m.val ((h : ℤ)-d) ≠ true := by
  rw [forbidden_iff_not_allowed,original_allowed_iff q l p h d input]
  simp only [not_exists,not_and]

def EntryAllowed (i : SMQLPatternRequests.Index) : Prop :=
  test q l i.1.2 (i.2.1.val+i.2.2.val) ((i.2.1.val : ℤ)-i.2.2.val) = true

theorem entry_allowed_iff (i : SMQLPatternRequests.Index) (hv : SMQLPatternRequests.Valid i)
    (input : SMQLPatternRequests.ReductionInput q l) :
    Allowed (SMFiniteSupportTable.TableTest (QLFiniteSupport.flavor q l) i) ↔ EntryAllowed q l i :=
  test_allowed_iff q l i.1.2 _ _ (input i hv)

theorem allowed_iff (select : ℤ × ℤ → Prop) (input : SMQLPatternRequests.ReductionInput q l) :
    Allowed (SMQLPatternRequests.Coefficients q l select) ↔
      ∃ i : SMQLPatternRequests.Entries select, EntryAllowed q l i.val := by
  rw [SelectionCriteria.allowed_family]
  exact exists_congr (fun i => entry_allowed_iff q l i.val i.property.1 input)

theorem forbidden_iff (select : ℤ × ℤ → Prop) (input : SMQLPatternRequests.ReductionInput q l) :
    Forbidden (SMQLPatternRequests.Coefficients q l select) ↔
      ∀ i : SMQLPatternRequests.Entries select, ¬ EntryAllowed q l i.val := by
  rw [forbidden_iff_not_allowed,allowed_iff q l select input]
  exact not_exists

def Conditions (request : SMQLPatternRequests.Request) : Prop :=
  (∀ t ∈ request.forbid, ∀ i : SMQLPatternRequests.Entries (ProhibitionPatterns.target t), ¬ EntryAllowed q l i.val) ∧
  (∀ t ∈ request.allow, ∃ i : SMQLPatternRequests.Entries (ProhibitionPatterns.target t), EntryAllowed q l i.val)

theorem satisfies_iff (request : SMQLPatternRequests.Request) (input : SMQLPatternRequests.ReductionInput q l) :
    SMQLPatternRequests.Satisfies q l request ↔ Conditions q l request := by
  unfold SMQLPatternRequests.Satisfies MixedSelectionRequests.Satisfies Conditions
  exact and_congr (forall_congr' (fun t => forall_congr' (fun _ => forbidden_iff q l _ input)))
    (forall_congr' (fun t => forall_congr' (fun _ => allowed_iff q l _ input)))

end
end GUT.SMComputableQLSupport
