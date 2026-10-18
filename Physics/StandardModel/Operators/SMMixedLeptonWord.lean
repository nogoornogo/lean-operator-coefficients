import Physics.StandardModel.Operators.SMMixedLeptonSupport

/-! Order-independent consumers for the signed mixed-lepton classification. -/
namespace GUT.SMMixedLeptonWord
set_option autoImplicit false
noncomputable section
open Math Representation SMMixedLeptonDictionary
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

/-- Equal occupation counts identify the original supported subspaces themselves. -/
theorem original_eq {n : ℕ} (p w : Fin n → DeltaLOneSignedInput.Species)
    (hc : ∀ s, SMIteratedContent.counts p s=SMIteratedContent.counts w s) (h d : ℕ) :
    SMFiniteHiggsSupport.OriginalSpace flavor p h d=
      SMFiniteHiggsSupport.OriginalSpace flavor w h d := by
  have ho (labels : Fin n → DeltaLOneSignedInput.Species) :
      (∃ e : Equiv.Perm (Fin n),labels ∘ e=p) ↔
      (∃ e : Equiv.Perm (Fin n),labels ∘ e=w) := by
    rw [PatternExteriorSource.orbit_iff_counts,PatternExteriorSource.orbit_iff_counts]
    apply forall_congr'
    intro s
    change SMIteratedContent.counts labels s=SMIteratedContent.counts p s ↔
      SMIteratedContent.counts labels s=SMIteratedContent.counts w s
    rw [hc s]
  apply Submodule.ext
  intro f
  change (_ ∧ PatternCoefficientSupport.Supported _ p _ f) ↔
    (_ ∧ PatternCoefficientSupport.Supported _ w _ f)
  simp only [PatternCoefficientSupport.Supported,ho]

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
theorem original_ql_iff (a b : ℕ) (p : Fin (a+b) → DeltaLOneSignedInput.Species)
    (hc : ∀ s, SMIteratedContent.counts p s=
      (if s=3 then a else 0)+(if s=8 then b else 0)) (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) p h d) ↔
      a • l-b • l=0 ∧ a≤12 ∧ b≤12 ∧ a%2=0 ∧ b%2=0 ∧
      (h : ℤ)-d=(a : ℤ)-b ∧
      -((capacity a+capacity b : ℕ) : ℤ)≤(a : ℤ)-b ∧
      (a : ℤ)-b≤((capacity a+capacity b : ℕ) : ℤ) := by
  have he := original_eq (QLFiniteSupport.flavor q l) p (pattern a b)
    (fun s => (hc s).trans (counts a b s).symm) h d
  rw [he,SMMixedLeptonSupport.original_ql_iff]

omit flavor in
theorem balanced_ql_iff (a h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) (pattern a a) h d) ↔
      a≤12 ∧ a%2=0 ∧ h=d := by
  rw [SMMixedLeptonSupport.original_ql_iff]
  have hn : 0≤((capacity a+capacity a : ℕ) : ℤ) := Int.natCast_nonneg _
  have hneg := neg_nonpos.mpr hn
  simp only [sub_self,sub_eq_zero,Int.natCast_inj,hneg,hn,and_true,true_and]
  tauto

end
end GUT.SMMixedLeptonWord
