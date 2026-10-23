import Physics.StandardModel.Operators.Support.Joint.SMJointContentSupport
import Physics.StandardModel.Operators.Support.Lepton.SMLowerHiggsSupport

/-! Complete structural support for every actual signed SM content and Higgs
bidegree, with the existing scalar cyclic q/l action. The criterion consists
of neutral charges and finite positive occupation/component/coupling tests.
There is no Weyl, character, rank or supplied branching premise. -/
namespace Physics.SMJointHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation BoundedHiggsSupport

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def compactLocalEquiv (m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants (SMCombinedCompactAction.action flavor p m delta) ≃ₗ[ℂ]
      InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta) :=
  (SMCombinedCompactAction.coefficientEquiv flavor p m delta).trans
    (SMMixedCompactCoefficients.localEquiv flavor p m delta).symm

def restrictCoefficient (m : ℕ) (delta : ℤ)
    (f : InvariantCoefficientTransport.Invariants (SMCombinedCompactAction.action flavor p m delta)) :
    InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor p m delta).comp SMGenerationCauchy.inclusion) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (SMGenerationCauchy.inclusion g)

theorem restricted_allowed (m : ℕ) (delta : ℤ)
    (h : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMCombinedCompactAction.action flavor p m delta))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor p m delta).comp SMGenerationCauchy.inclusion)) := by
  obtain ⟨f,hf⟩ := h
  refine ⟨restrictCoefficient flavor p m delta f,?_⟩
  intro he
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun he x

/-- Arbitrary residual flavor data are irrelevant here because this is the
local coefficient space. The separate scalar q/l condition is reattached
below; no arbitrary residual action is classified by this lemma. -/
theorem local_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) ↔
    SMContentWeakBound.hypercharge p + 3*delta = 0 ∧
      SMJointContentSupport.Supports (SMIteratedContent.counts p) m := by
  constructor
  · intro h
    refine ⟨SMChargedKernelRank.local_charge flavor p m delta h,?_⟩
    exact (SMJointContentSupport.restricted_iff flavor p m delta).mp
      (restricted_allowed flavor p m delta
        ((SelectionCriteria.allowed_equiv (compactLocalEquiv flavor p m delta)).mpr h))
  · rintro ⟨hc,hs⟩
    exact (SelectionCriteria.allowed_equiv (compactLocalEquiv flavor p m delta)).mp
      (SMCombinedChargeSupport.allowed flavor p m delta hc
        ((SMJointContentSupport.restricted_iff flavor p m delta).mpr hs))

omit flavor in
def HiggsSupport (h d : ℕ) : Prop :=
  ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
    SMJointContentSupport.Supports (SMIteratedContent.counts p) m.val

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
/-- The original all-degree statistical coefficient space is nonzero exactly
when the two scalar charges are neutral and the positive finite joint test
has a witness. This covers all ten signed species and mixed contents. -/
theorem original_ql_iff (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
    QLFiniteSupport.charge q l p = 0 ∧
      SMContentWeakBound.hypercharge p + 3*((h : ℤ)-d) = 0 ∧ HiggsSupport p h d := by
  rw [SMLowerHiggsSupport.ql_original_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨m,hm,ha⟩
    obtain ⟨hc,hs⟩ := (local_iff (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d)).mp ha
    exact ⟨hc,m,hm,hs⟩
  · rintro ⟨hc,m,hm,hs⟩
    exact ⟨m,hm,(local_iff (QLFiniteSupport.flavor q l) p m.val ((h : ℤ)-d)).mpr ⟨hc,hs⟩⟩

omit flavor in
theorem original_ql_forbidden_iff (h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
    QLFiniteSupport.charge q l p ≠ 0 ∨
      SMContentWeakBound.hypercharge p + 3*((h : ℤ)-d) ≠ 0 ∨ ¬ HiggsSupport p h d := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,original_ql_iff]
  simp only [not_and_or]

end
end Physics.SMJointHiggsSupport
