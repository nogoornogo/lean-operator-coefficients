import Physics.StandardModel.Operators.SMSparseCharacter

/-! The optimized evaluator preserves the proved actual kernel/support semantics. -/
namespace GUT.SMSparseSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMSparseCharacter
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)
  (input : SMCompactMultiplicity.Input flavor p m delta)

include input in
theorem kernel_dimension_int : (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) : ℤ) =
    multiplicity (SMIteratedContent.counts p) m delta := by
  exact (SMComputableSupport.kernel_dimension_int flavor p m delta input).trans
    (multiplicity_reference _ _ _).symm

include input in
theorem kernel_dimension : Module.finrank ℂ (SMFullLocalKernel.Kernel flavor p m delta) =
    (multiplicity (SMIteratedContent.counts p) m delta).toNat := by
  exact (SMComputableSupport.kernel_dimension flavor p m delta input).trans
    (congrArg Int.toNat (multiplicity_reference _ _ _)).symm

include input in
theorem rank_formula : Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
    SMIteratedContent.columns p m - (multiplicity (SMIteratedContent.counts p) m delta).toNat := by
  exact (SMComputableSupport.rank_formula flavor p m delta input).trans
    (congrArg (fun z : ℤ => SMIteratedContent.columns p m - z.toNat) (multiplicity_reference _ _ _)).symm

include input in
theorem local_allowed_iff : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor p m delta)) ↔ 0 < multiplicity (SMIteratedContent.counts p) m delta := by
  exact (SMComputableSupport.local_allowed_iff flavor p m delta input).trans
    ((congrArg (fun z : ℤ => 0 < z) (multiplicity_reference _ _ _)).to_iff).symm

end
end GUT.SMSparseSupport

namespace GUT.SMSparseQLSupport
set_option autoImplicit false
open Math Representation SelectionCriteria
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def test (m : ℕ) (delta : ℤ) : Bool :=
  decide (QLFiniteSupport.charge q l p = 0 ∧
    0 < SMSparseCharacter.multiplicity (SMIteratedContent.counts p) m delta)

omit [NeZero k] in
theorem test_reference (m : ℕ) (delta : ℤ) :
    test q l p m delta = SMComputableQLSupport.test q l p m delta := by
  simp only [test,SMComputableQLSupport.test,SMSparseCharacter.multiplicity_reference]

noncomputable section
theorem test_allowed_iff (m : ℕ) (delta : ℤ) (input : SMComputableQLSupport.Input q l p m delta) :
    Allowed (QLFiniteSupport.Test q l p m delta) ↔ test q l p m delta = true := by
  rw [test_reference]
  exact SMComputableQLSupport.test_allowed_iff q l p m delta input

theorem original_allowed_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1), SMComputableQLSupport.Input q l p m.val ((h : ℤ)-d)) :
    Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
        test q l p m.val ((h : ℤ)-d) = true := by
  simp only [test_reference]
  exact SMComputableQLSupport.original_allowed_iff q l p h d input

end
end GUT.SMSparseQLSupport
