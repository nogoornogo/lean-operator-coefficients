import Physics.StandardModel.Operators.WeinbergFullSeed

/-! Residual Higgs neutrality does not imply zero-Higgs reduction for the
actual weak doublet. This does not refute a larger finite primitive set. -/
namespace GUT.HiggsEigenlineBoundary
set_option autoImplicit false
noncomputable section
open Math
variable {k : ℕ} [NeZero k] (q l : ZMod k)

theorem zero_higgs_forbidden :
    SelectionCriteria.Forbidden
      (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 0 0) :=
  ContentHiggsSupport.leptonPair_balanced_forbidden q l 0

theorem two_higgs_allowed (hc : 2*l=0) :
    SelectionCriteria.Allowed
      (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 2 0) :=
  (WeinbergFullSeed.allowed_iff q l 2 0).mpr ⟨by omega,hc⟩

/-- Neutral residual Higgs action alone cannot identify these two support predicates. -/
theorem no_zero_degree_iff (hc : 2*l=0) :
    ¬ (SelectionCriteria.Allowed
        (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 2 0) ↔
      SelectionCriteria.Allowed
        (ContentHiggsSupport.Space q l ContentHiggsSupport.leptonPair 0 0)) := by
  intro he
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp (zero_higgs_forbidden q l)
    (he.mp (two_higgs_allowed q l hc))

end
end GUT.HiggsEigenlineBoundary
