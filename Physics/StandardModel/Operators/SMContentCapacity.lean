import Physics.StandardModel.Operators.SMMixedWeakCapacity

/-! Structural capacity of every actual statistical source. Binomial factors
stay symbolic; no closed dimension, character or matrix is evaluated. -/
namespace GUT.SMContentCapacity
set_option autoImplicit false
noncomputable section
open Math Representation

def Fits {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) : Prop :=
  ∀ s, SMIteratedContent.counts p s ≤ SMConstantWeakCapacity.dimension s

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

local instance fieldFinite (s : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field,ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

local instance sourceFinite : FiniteDimensional ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) p).toLinearMap)
  infer_instance

theorem source_allowed_iff :
    SelectionCriteria.Allowed (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) ↔
      Fits p := by
  rw [SelectionCriteria.Allowed,← Module.finrank_pos_iff_exists_ne_zero (R := ℂ),
    SMIteratedContent.source_dimension]
  change (0 < ∏ s,
    ((![36,18,18,12,6,36,18,18,12,6] : DeltaLOneSignedInput.Species → ℕ) s).choose
      (SMIteratedContent.counts p s)) ↔ Fits p
  simp only [Nat.pos_iff_ne_zero,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies,Fits,
    ← SMConstantWeakCapacity.dimension_eq,Nat.choose_ne_zero_iff]

theorem source_finrank_zero (hc : ¬ Fits p) :
    Module.finrank ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p)=0 := by
  by_contra hz
  have ha := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (Nat.pos_of_ne_zero hz)
  exact hc ((source_allowed_iff flavor p).mp ha)

theorem local_forbidden (hc : ¬ Fits p) (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) := by
  have hs : Subsingleton (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :=
    (Module.finrank_zero_iff).mp (source_finrank_zero flavor p hc)
  let := hs
  intro f
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx : x=0 := Subsingleton.elim _ _
  simp only [hx,map_zero]

omit flavor in
theorem original_ql_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ) (hc : ¬ Fits p) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,QLFiniteSupport.original_allowed_iff]
  rintro ⟨_,m,_,ha⟩
  have hl := (SelectionCriteria.allowed_equiv
    (SMLowerHiggsSupport.qlLocalEquiv p q l m.val ((h : ℤ)-d))).mp ha
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (local_forbidden (QLFiniteSupport.flavor q l) p hc m.val ((h : ℤ)-d)) hl

end
end GUT.SMContentCapacity
