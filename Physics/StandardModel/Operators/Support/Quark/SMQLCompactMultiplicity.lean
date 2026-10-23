import Physics.StandardModel.Operators.Support.Decomposition.SMCompactMultiplicity
import Physics.StandardModel.Operators.Support.Quark.SMQLFullKernel

/-! Full support for the existing scalar cyclic q/l residual action, through
actual local character extraction and the original all-degree Higgs reduction. -/
namespace Physics.SMQLCompactMultiplicity
set_option autoImplicit false
noncomputable section
open Math Representation
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev multiplicity (m : ℕ) (delta : ℤ) :=
  SMCompactMultiplicity.multiplicity (QLFiniteSupport.flavor q l) p m delta
abbrev Input (m : ℕ) (delta : ℤ) := SMCompactMultiplicity.Input (QLFiniteSupport.flavor q l) p m delta

theorem test_allowed_iff (m : ℕ) (delta : ℤ) (input : Input q l p m delta) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l p m delta) ↔
      QLFiniteSupport.charge q l p = 0 ∧ 0 < multiplicity q l p m delta :=
  (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr Iff.rfl (SMCompactMultiplicity.local_allowed_iff
      (QLFiniteSupport.flavor q l) p m delta input))

theorem original_allowed_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1), Input q l p m.val ((h : ℤ)-d)) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          0 < multiplicity q l p m.val ((h : ℤ)-d) :=
  (QLFiniteSupport.original_allowed_iff q l p h d).trans
    (and_congr Iff.rfl (exists_congr (fun m => and_congr Iff.rfl
      (SMCompactMultiplicity.local_allowed_iff (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d) (input m)))))

theorem original_forbidden_iff (h d : ℕ)
    (input : ∀ m : Fin (SMContentWeakBound.bound p+1), Input q l p m.val ((h : ℤ)-d)) :
    SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ¬ (QLFiniteSupport.charge q l p = 0 ∧
        ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
          0 < multiplicity q l p m.val ((h : ℤ)-d)) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,original_allowed_iff q l p h d input]

end
end Physics.SMQLCompactMultiplicity
