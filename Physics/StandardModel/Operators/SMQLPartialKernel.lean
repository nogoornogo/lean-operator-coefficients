import Physics.StandardModel.Operators.SMWeylFiniteKernel
import Math.RepresentationTheory.PartialInvariantKernel

/-! Exact q/l all-degree reduction to finite Weyl rows with actual gauge conditions retained. -/
namespace GUT.SMQLPartialKernel
set_option autoImplicit false
noncomputable section
open Math Representation
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev localAction (m : ℕ) (delta : ℤ) :=
  (QLFiniteSupport.action q l p m delta).comp
    (MonoidHom.inl (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) (CyclicCharge.Group k))

def Space (m : ℕ) (delta : ℤ) :=
  PartialInvariantKernel.Space (localAction q l p m delta)
    (SMWeylFiniteKernel.basis (QLFiniteSupport.flavor q l) p m) (WeylRealTransvections.tests n)

def coefficientEquiv (m : ℕ) (delta : ℤ) :
    QLFiniteSupport.LocalTest q l p m delta ≃ₗ[ℂ] Space q l p m delta :=
  PartialInvariantKernel.equiv _ _ _
    (SMWeylFiniteKernel.exhaustive (QLFiniteSupport.flavor q l) p m delta)

theorem local_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (QLFiniteSupport.LocalTest q l p m delta) ↔
      SelectionCriteria.Allowed (Space q l p m delta) :=
  SelectionCriteria.allowed_equiv (coefficientEquiv q l p m delta)

/-- Original statistical/Higgs coefficients, with gauge invariance still explicit in Space. -/
theorem original_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) p h d) ↔
    QLFiniteSupport.charge q l p = 0 ∧
      ∃ m : Fin (SMContentWeakBound.bound p+1), BoundedHiggsSupport.Admissible h d m.val ∧
        SelectionCriteria.Allowed (Space q l p m.val ((h : ℤ)-d)) := by
  exact (QLFiniteSupport.original_allowed_iff q l p h d).trans
    (and_congr Iff.rfl (exists_congr (fun m =>
      and_congr Iff.rfl (local_allowed_iff q l p m.val ((h : ℤ)-d)))))

end
end GUT.SMQLPartialKernel
