import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionBounds

/-! Arithmetic on ten abstract species counts. No original coefficient space
occurs in these hypotheses or proofs. -/
namespace Physics.SMB1WeakCountArithmetic
set_option autoImplicit false
open Math DeltaLOneSignedInput
open scoped BigOperators

def total (c : Species → ℕ) : ℕ :=
  c 0+c 1+c 2+c 3+c 4+c 5+c 6+c 7+c 8+c 9
def baryon (c : Species → ℕ) : ℤ := (c 0 : ℤ)+c 1+c 2-c 5-c 6-c 7
def lepton (c : Species → ℕ) : ℤ := (c 3 : ℤ)+c 4-c 8-c 9
def hypercharge (c : Species → ℕ) : ℤ :=
  (c 0 : ℤ)+4*c 1-2*c 2-3*c 3-6*c 4-c 5-4*c 6+2*c 7+3*c 8+6*c 9

theorem capacity_sums (c : Species → ℕ) (h3 : c 3≤12) (h8 : c 8≤12) :
    (∑ s, SMMixedWeakCapacity.speciesBound s (c s) : ℕ) ≤
      c 0+c 5+(12-c 3)+c 8 ∧
    (∑ s, SMMixedWeakCapacity.speciesBound s (c s) : ℕ) ≤
      c 0+c 5+c 3+(12-c 8) := by
  simp [SMMixedWeakCapacity.speciesBound,SMConstantWeakCapacity.bound,
    SMConstantWeakCapacity.dimension_eq,SMWeakWeightBasis.doubletCount,
    Fin.sum_univ_succ]
  constructor <;> omega

/-- The large mixed proof is replaced by two explicit nonnegative identities. -/
theorem weak_envelope (c : Species → ℕ) (h d : ℕ)
    (hy : hypercharge c+3*((h : ℤ)-d)=0)
    (hp : (h : ℤ)-d ≤ (c 0 : ℤ)+c 5+12-c 3+c 8)
    (hn : (d : ℤ)-h ≤ (c 0 : ℤ)+c 5+12+c 3-c 8) :
    |7*lepton c-baryon c| ≤ 12+3*(total c : ℤ)+2*((h : ℤ)+d) := by
  have hpos : 0 ≤ (c 0 : ℤ)+c 5+12-c 3+c 8-h+d := by omega
  have hneg : 0 ≤ (c 0 : ℤ)+c 5+12+c 3-c 8+h-d := by omega
  have hp0 : 0 ≤ 2*(c 0 : ℤ)+6*c 2+2*c 4+2*c 5+6*c 6+6*c 8+4*c 9+4*d := by positivity
  have hn0 : 0 ≤ 2*(c 5 : ℤ)+6*c 7+2*c 9+2*c 0+6*c 1+6*c 3+4*c 4+4*h := by positivity
  have hp1 := add_nonneg hpos hp0
  have hn1 := add_nonneg hneg hn0
  have ep : ((c 0 : ℤ)+c 5+12-c 3+c 8-h+d)+
      (2*(c 0 : ℤ)+6*c 2+2*c 4+2*c 5+6*c 6+6*c 8+4*c 9+4*d) =
      12+3*(total c : ℤ)+2*((h : ℤ)+d)-7*lepton c+baryon c := by
    unfold total lepton baryon hypercharge at *
    push_cast
    linear_combination -hy
  have en : ((c 0 : ℤ)+c 5+12+c 3-c 8+h-d)+
      (2*(c 5 : ℤ)+6*c 7+2*c 9+2*c 0+6*c 1+6*c 3+4*c 4+4*h) =
      12+3*(total c : ℤ)+2*((h : ℤ)+d)+7*lepton c-baryon c := by
    unfold total lepton baryon hypercharge at *
    push_cast
    linear_combination hy
  rw [ep] at hp1
  rw [en] at hn1
  rw [abs_le]
  constructor <;> omega

end Physics.SMB1WeakCountArithmetic
