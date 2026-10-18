import Math.RepresentationTheory.CyclicCharge
import Physics.StandardModel.Operators.ScalarResidualSelection

open Math

/-! Complete one-generation cyclic selection conditions. Higgs is residual
neutral. Signed fermion charges are fixed independently of coefficient assembly. -/
namespace GUT.CyclicResidualSelection
set_option autoImplicit false
noncomputable section
open CyclicCharge ScalarResidualSelection SelectionCriteria
variable {N : ℕ} [NeZero N]

abbrev Charges (N : ℕ) := Fin 5 → ZMod N

def signedCharges (c : Charges N) : DeltaLOneSignedInput.Species → ZMod N :=
  ![c 0,c 1,c 2,c 3,c 4,-c 0,-c 1,-c 2,-c 3,-c 4]

def flavor (c : Charges N) (s : DeltaLOneSignedInput.Species) :=
  representation (signedCharges c s)

/-- DUQL, QQUE, QQQL, DUUE, in the physical right-handed convention. -/
def familyCharge (c : Charges N) : Fin 4 → ZMod N :=
  ![(c 2+c 1)+(c 0+c 3), (c 0+c 0)+(c 1+c 4),
    (c 0+c 0)+(c 0+c 3), (c 1+c 1)+(c 2+c 4)]

theorem neutral_four_iff (a b c d : ZMod N) :
    Neutral (representation a) (representation b) (representation c) (representation d) ↔
      (a+b)+(c+d) = 0 := by
  unfold Neutral
  simp only [action, mul_one]
  simp_rw [← AddChar.map_add_eq_mul, ← add_mul]
  exact neutral_iff _

theorem allowed_total_iff (c : Charges N) :
    Allowed (DeltaLOneSignedFields.Sector (flavor c) 1) ↔
      ∃ i : Fin 4, familyCharge c i = 0 := by
  rw [allowed_total]
  change Neutral (representation (c 2)) (representation (c 1))
      (representation (c 0)) (representation (c 3)) ∨
    Neutral (representation (c 0)) (representation (c 0))
      (representation (c 1)) (representation (c 4)) ∨
    Neutral (representation (c 0)) (representation (c 0))
      (representation (c 0)) (representation (c 3)) ∨
    Neutral (representation (c 1)) (representation (c 1))
      (representation (c 2)) (representation (c 4)) ↔ _
  simp only [neutral_four_iff]
  simp [familyCharge, Fin.exists_fin_succ]

theorem allowed_family_iff (c : Charges N) (i : Fin 4) :
    Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) i) ↔
      familyCharge c i = 0 := by
  fin_cases i
  · change Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) 0) ↔ _
    rw [(ofEquiv (DeltaLOneFamilyCompleteness.duqlEquiv (flavor c))).allowed]
    change Allowed (Four (representation (c 2)) (representation (c 1))
      (representation (c 0)) (representation (c 3))) ↔ _
    rw [allowed_four]
    exact neutral_four_iff _ _ _ _
  · change Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) 1) ↔ _
    rw [(ofEquiv (DeltaLOneFamilyCompleteness.qqueEquiv (flavor c))).allowed]
    rw [allowed_qque]
    exact neutral_four_iff _ _ _ _
  · change Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) 2) ↔ _
    rw [(ofEquiv (DeltaLOneFamilyCompleteness.qqqlEquiv (flavor c))).allowed]
    rw [allowed_qqql]
    exact neutral_four_iff _ _ _ _
  · change Allowed (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) 3) ↔ _
    rw [(ofEquiv (DeltaLOneFamilyCompleteness.duueEquiv (flavor c))).allowed]
    change Allowed (Four (representation (c 1)) (representation (c 1))
      (representation (c 2)) (representation (c 4))) ↔ _
    rw [allowed_four]
    exact neutral_four_iff _ _ _ _

theorem forbidden_family_iff (c : Charges N) (i : Fin 4) :
    Forbidden (DeltaLOneFourFamilyDecomposition.FamilySector (flavor c) i) ↔
      familyCharge c i ≠ 0 := by
  rw [forbidden_iff_not_allowed, allowed_family_iff]

theorem forbidden_total_iff (c : Charges N) :
    Forbidden (DeltaLOneSignedFields.Sector (flavor c) 1) ↔
      ∀ i : Fin 4, familyCharge c i ≠ 0 := by
  rw [forbidden_iff_not_allowed, allowed_total_iff]
  simp

theorem allowed_weinberg_iff (l : ZMod N) :
    Allowed (WeinbergSMInterface.ModelSector (representation l)) ↔ l+l = 0 := by
  rw [(ofEquiv (WeinbergSMInterface.coefficientEquiv (representation l))).allowed]
  rw [Allowed, WeinbergScalarFlavor.exists_nonzero_iff_square_trivial]
  simp only [action, mul_one, pow_two]
  simp_rw [← AddChar.map_add_eq_mul, ← add_mul]
  exact neutral_iff _

theorem simultaneous_iff (c : Charges N) :
    (Forbidden (DeltaLOneSignedFields.Sector (flavor c) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation (c 3)))) ↔
    ((∀ i : Fin 4, familyCharge c i ≠ 0) ∧ c 3+c 3 = 0) := by
  rw [forbidden_total_iff, allowed_weinberg_iff]

/-- Z2 quark parity: all four baryon-violating families are odd, LLHH is even. -/
def quarkParity : Charges 2 := ![1,1,1,0,0]

theorem quarkParity_conditions :
    (∀ i : Fin 4, familyCharge quarkParity i ≠ 0) ∧
      quarkParity 3+quarkParity 3 = 0 := by
  constructor
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel

theorem quarkParity_selection :
    Forbidden (DeltaLOneSignedFields.Sector (flavor quarkParity) 1) ∧
    Allowed (WeinbergSMInterface.ModelSector (representation (quarkParity 3))) :=
  (simultaneous_iff _).mpr quarkParity_conditions

theorem trivial_assignment_rejected (N : ℕ) [NeZero N] :
    ¬ (Forbidden (DeltaLOneSignedFields.Sector (flavor (0 : Charges N)) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation ((0 : Charges N) 3)))) := by
  rw [simultaneous_iff]
  simp [familyCharge, Fin.forall_fin_succ]

theorem order_one_rejected (c : Charges 1) :
    ¬ (Forbidden (DeltaLOneSignedFields.Sector (flavor c) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation (c 3)))) := by
  rw [simultaneous_iff]
  intro h
  exact h.1 0 (Subsingleton.elim _ _)

end
end GUT.CyclicResidualSelection
