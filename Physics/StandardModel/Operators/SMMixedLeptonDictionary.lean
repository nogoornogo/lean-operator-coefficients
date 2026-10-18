import Physics.StandardModel.Operators.SMContentCapacity
import Physics.StandardModel.Operators.SMChiralitySupport
import Math.RepresentationTheory.BinaryPatternExterior

/-! Exact dictionaries for the actual signed L/conjugate-L content.
Occupations stay symbolic; no character or rank is evaluated. -/
namespace GUT.SMMixedLeptonDictionary
set_option autoImplicit false
noncomputable section
open Math Representation

abbrev pattern (a b : ℕ) := BinaryPatternExterior.pattern (3 : DeltaLOneSignedInput.Species) 8 a b
abbrev capacity (a : ℕ) := min a (12-a)

theorem counts (a b : ℕ) (s : DeltaLOneSignedInput.Species) :
    SMIteratedContent.counts (pattern a b) s =
      (if s=3 then a else 0)+(if s=8 then b else 0) := by
  unfold SMIteratedContent.counts
  rw [Finset.card_filter]
  simp only [pattern, BinaryPatternExterior.pattern, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right]
  by_cases h3 : s=3 <;> by_cases h8 : s=8 <;> simp_all [eq_comm]

theorem raw_bound (a b : ℕ) : SMContentWeakBound.bound (pattern a b)=a+b := by
  simp [SMContentWeakBound.bound,pattern,BinaryPatternExterior.pattern,Fin.sum_univ_add,
    SMWeakWeightBasis.doubletCount]

theorem sharp_bound (a b : ℕ) : SMMixedWeakCapacity.bound (pattern a b)=capacity a+capacity b := by
  simp only [SMMixedWeakCapacity.bound,counts]
  simp [SMMixedWeakCapacity.speciesBound,SMWeakWeightBasis.doubletCount,
    SMConstantWeakCapacity.bound,SMConstantWeakCapacity.dimension_eq,capacity,
    Fin.sum_univ_succ]

theorem hypercharge (a b : ℕ) :
    SMContentWeakBound.hypercharge (pattern a b) = -3*(a : ℤ)+3*(b : ℤ) := by
  simp [SMContentWeakBound.hypercharge,pattern,BinaryPatternExterior.pattern,
    Fin.sum_univ_add,DeltaLOneSignedInput.hypercharge]
  ring

theorem chirality (a b : ℕ) (side : Bool) :
    SMChiralitySupport.count (pattern a b) side=if side then b else a := by
  cases side <;> simp [SMChiralitySupport.count,SMChiralitySupport.slotCount,pattern,
    BinaryPatternExterior.pattern,Fin.sum_univ_add,DeltaLOneSignedFields.rightHanded]

theorem fits (a b : ℕ) : SMContentCapacity.Fits (pattern a b) ↔ a≤12 ∧ b≤12 := by
  simp only [SMContentCapacity.Fits,counts,SMConstantWeakCapacity.dimension_eq]
  constructor
  · intro h
    exact ⟨by simpa using h 3,by simpa using h 8⟩
  · rintro ⟨ha,hb⟩ s
    fin_cases s <;> simp_all

theorem residual {k : ℕ} (q l : ZMod k) (a b : ℕ) :
    QLFiniteSupport.charge q l (pattern a b)=a • l-b • l := by
  simp [QLFiniteSupport.charge,pattern,BinaryPatternExterior.pattern,Fin.sum_univ_add,
    DuqlHiggsContent.signedCharge,sub_eq_add_neg]

end
end GUT.SMMixedLeptonDictionary
