import Physics.StandardModel.Operators.SMFullLocalKernel

/-! Complete original q/l all-degree coefficient support as an exact finite rank predicate. -/
namespace GUT.SMQLFullKernel
set_option autoImplicit false
noncomputable section
open Math Representation
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev Kernel (m : ℕ) (delta : ℤ) := SMFullLocalKernel.Kernel (QLFiniteSupport.flavor q l) p m delta

def coefficientEquiv (m : ℕ) (delta : ℤ) :
    QLFiniteSupport.LocalTest q l p m delta ≃ₗ[ℂ] Kernel q l p m delta :=
  SMFullLocalKernel.coefficientEquiv (QLFiniteSupport.flavor q l) p m delta

def RankAllowed (m : ℕ) (delta : ℤ) : Prop :=
  Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints
    (QLFiniteSupport.flavor q l) p m delta)) <
      Fintype.card (Fin (Module.finrank ℂ
        (SMFullLocalKernel.Carrier (QLFiniteSupport.flavor q l) p m)))

theorem local_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (QLFiniteSupport.LocalTest q l p m delta) ↔ RankAllowed q l p m delta :=
  by
    unfold RankAllowed
    exact SMFullLocalKernel.allowed_iff_rank_lt (QLFiniteSupport.flavor q l) p m delta

/-- No actual gauge-invariance, polynomiality or exhaustive-test premise remains. -/
theorem original_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) p h d) ↔
    QLFiniteSupport.charge q l p = 0 ∧
      ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
        RankAllowed q l p m.val ((h : ℤ)-d) :=
  (QLFiniteSupport.original_allowed_iff q l p h d).trans
    (and_congr Iff.rfl (exists_congr (fun m => and_congr Iff.rfl
      (local_allowed_iff q l p m.val ((h : ℤ)-d)))))

/-- Each previously retained Allowed(T) is now an explicit exact rank test. -/
theorem test_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l p m delta) ↔
      QLFiniteSupport.charge q l p=0 ∧ RankAllowed q l p m delta :=
  (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr Iff.rfl (local_allowed_iff q l p m delta))

end
end GUT.SMQLFullKernel
