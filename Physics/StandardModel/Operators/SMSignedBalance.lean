import Math.RepresentationTheory.PatternCountSum
import Physics.StandardModel.Operators.SMSaturatedContentSupport

/-! Matched signed counts cancel hypercharge and cyclic q/l charges even at
even cyclic order. For saturated balanced contents the complete support is
decided. Balanced partially occupied contents are not asserted allowed. -/
namespace GUT.SMSignedBalance
set_option autoImplicit false
noncomputable section
open Math Representation

def Balanced {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) : Prop :=
  ∀ s : Fin 5, SMIteratedContent.counts p (Fin.castAdd 5 s) =
    SMIteratedContent.counts p (Fin.natAdd 5 s)

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem hypercharge_zero (hb : Balanced p) : SMContentWeakBound.hypercharge p=0 :=
  PatternCountSum.paired_zero (r := 5) p DeltaLOneSignedInput.hypercharge hb (by
    intro s; fin_cases s <;> rfl)

theorem ql_charge_zero {k : ℕ} [NeZero k] (q l : ZMod k) (hb : Balanced p) :
    QLFiniteSupport.charge q l p=0 :=
  PatternCountSum.paired_zero (r := 5) p (DuqlHiggsContent.signedCharge q l) hb (by
    intro s; fin_cases s <;> rfl)

theorem saturated_original_ql_iff {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ)
    (hc : SMSaturatedContentSupport.Saturated p) (hb : Balanced p) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔ h=d := by
  rw [SMSaturatedContentSupport.original_ql_iff p q l h d hc,
    hypercharge_zero p hb,ql_charge_zero p q l hb]
  simp

theorem full_balanced (hf : ∀ s, SMIteratedContent.counts p s=SMConstantWeakCapacity.dimension s) :
    Balanced p := by
  intro s
  rw [hf,hf,SMConstantWeakCapacity.dimension_eq,SMConstantWeakCapacity.dimension_eq]
  fin_cases s <;> rfl

/-- The fully occupied signed universe is an actual allowed coefficient
family exactly on the Higgs-pair direction, at every cyclic order. No degree
or coefficient dimension is expanded or numerically verified. -/
theorem full_original_ql_iff {k : ℕ} [NeZero k] (q l : ZMod k) (h d : ℕ)
    (hf : ∀ s, SMIteratedContent.counts p s=SMConstantWeakCapacity.dimension s) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔ h=d :=
  saturated_original_ql_iff p q l h d (fun s => Or.inr (hf s)) (full_balanced p hf)

end
end GUT.SMSignedBalance
