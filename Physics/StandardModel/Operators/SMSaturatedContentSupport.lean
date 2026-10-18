import Physics.StandardModel.Operators.SMMixedWeakCapacity
import Physics.StandardModel.Operators.SMCompactLineSupport
import Physics.StandardModel.Operators.SMCombinedCompactContinuity

/-! Complete structural support for every mixed content whose species are
empty or fully occupied. Source lines follow from top exterior powers; all
hypercharge/residual twists are retained. No Weyl or numerical certificate. -/
namespace GUT.SMSaturatedContentSupport
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct

private theorem transport_allowed {I : Type*} (A : I → Type*) [∀ i, Zero (A i)]
    {i j : I} (h : i=j) (ha : SelectionCriteria.Allowed (A j)) :
    SelectionCriteria.Allowed (A i) := h.symm ▸ ha

def Saturated {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) : Prop :=
  ∀ s, SMIteratedContent.counts p s=0 ∨
    SMIteratedContent.counts p s=SMConstantWeakCapacity.dimension s

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem source_dimension (hc : Saturated p) :
    Module.finrank ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p)=1 := by
  rw [SMIteratedContent.source_dimension]
  change (∏ s, ((![36,18,18,12,6,36,18,18,12,6] : DeltaLOneSignedInput.Species → ℕ) s).choose
    (SMIteratedContent.counts p s))=1
  apply Finset.prod_eq_one
  intro s _
  rw [← SMConstantWeakCapacity.dimension_eq s]
  rcases hc s with hs | hs <;> simp [hs]

theorem model_zero_dimension (hc : Saturated p) : Module.finrank ℂ
    (FiniteBasisHilbertization.Copy (SMCombinedCompactContinuity.sourceBasis flavor p) ⊗[ℂ]
      EuclideanSpace ℂ (Fin (0+1)))=1 := by
  have hs := (FiniteBasisHilbertization.Copy.valLinearEquiv
    (SMCombinedCompactContinuity.sourceBasis flavor p)).finrank_eq.trans (source_dimension flavor p hc)
  rw [Module.finrank_tensorProduct,hs]
  simp

theorem neutral_local_allowed (hc : Saturated p) (hy : SMContentWeakBound.hypercharge p=0) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p 0 0)) := by
  have hh (z : Circle) : SMCombinedCompactContinuity.model flavor p 0 0
      (SMCombinedChargeSupport.hyper z)=LinearMap.id := by
    apply ContinuousLineActions.transport_id (SMCombinedCompactContinuity.equiv flavor p 0 0)
    apply LinearMap.ext
    intro x
    change SMCombinedCompactAction.action flavor p 0 0 (SMCombinedChargeSupport.hyper z) x=x
    simpa only [hy,mul_zero,add_zero,zpow_zero,one_smul] using
      SMCombinedChargeSupport.action_hyper flavor p 0 0 z x
  have ha := SMCompactLineSupport.allowed (SMCombinedCompactContinuity.model flavor p 0 0)
    (SMCombinedCompactContinuity.continuous_model flavor p 0 0) (model_zero_dimension flavor p hc) hh
  exact (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactContinuity.coefficientEquiv flavor p 0 0).trans
      (SMMixedCompactCoefficients.localEquiv flavor p 0 0).symm)).mp ha

omit flavor in
theorem original_ql_iff {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ) (hc : Saturated p) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      h=d ∧ SMContentWeakBound.hypercharge p=0 ∧ QLFiniteSupport.charge q l p=0 := by
  constructor
  · intro ha
    have hhd : h=d := by
      by_contra hd
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMMixedWeakCapacity.saturated_original_ql_forbidden p q l h d (fun s _ => hc s) hd) ha
    obtain ⟨hq,m,_,hl⟩ := (QLFiniteSupport.original_allowed_iff q l p h d).mp ha
    have hlocal := (SelectionCriteria.allowed_equiv
      (SMLowerHiggsSupport.qlLocalEquiv p q l m.val ((h : ℤ)-d))).mp hl
    have hy := SMChargedKernelRank.local_charge (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d) hlocal
    exact ⟨hhd,by rw [hhd] at hy; simpa using hy,hq⟩
  · rintro ⟨hhd,hy,hq⟩
    subst d
    apply (QLFiniteSupport.original_allowed_iff q l p h h).mpr
    refine ⟨hq,⟨0,by omega⟩,?_,?_⟩
    · dsimp [BoundedHiggsSupport.Admissible]; omega
    · change SelectionCriteria.Allowed (QLFiniteSupport.LocalTest q l p 0 ((h : ℤ)-h))
      exact transport_allowed (fun delta : ℤ => QLFiniteSupport.LocalTest q l p 0 delta)
        (sub_self (h : ℤ))
        ((SelectionCriteria.allowed_equiv (SMLowerHiggsSupport.qlLocalEquiv p q l 0 0)).mpr
          (neutral_local_allowed (QLFiniteSupport.flavor q l) p hc hy))

omit flavor in
theorem original_ql_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ) (hc : Saturated p) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      ¬ (h=d ∧ SMContentWeakBound.hypercharge p=0 ∧ QLFiniteSupport.charge q l p=0) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,original_ql_iff p q l h d hc]

end
end GUT.SMSaturatedContentSupport
