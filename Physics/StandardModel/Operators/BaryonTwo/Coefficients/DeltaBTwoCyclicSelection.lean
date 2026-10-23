import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoScalarSelection

open Math

namespace Physics.DeltaBTwoCyclicSelection
set_option autoImplicit false
noncomputable section
open SelectionCriteria CyclicCharge
variable {N : ℕ} [NeZero N]

def charge (u d : ZMod N) := 2*u + 4*d

theorem neutral_iff (u d : ZMod N) :
    DeltaBTwoScalarSelection.Neutral (representation u) (representation d) ↔
      charge u d = 0 := by
  unfold DeltaBTwoScalarSelection.Neutral DeltaBTwoScalarSelection.total
  simp only [action, mul_one, pow_succ, pow_zero, one_mul]
  simp_rw [← AddChar.map_add_eq_mul]
  have he (g : CyclicCharge.Group N) :
      ((u * Multiplicative.toAdd g + u * Multiplicative.toAdd g) +
        (((d * Multiplicative.toAdd g + d * Multiplicative.toAdd g) +
          d * Multiplicative.toAdd g) + d * Multiplicative.toAdd g)) =
      charge u d * Multiplicative.toAdd g := by unfold charge; ring
  simp_rw [he]
  exact CyclicCharge.neutral_iff _

theorem allowed_iff (u d : ZMod N) :
    Allowed (DeltaBTwoModelInterface.ModelSector (representation u) (representation d)) ↔
      charge u d = 0 := by
  rw [DeltaBTwoScalarSelection.allowed_iff, neutral_iff]

theorem forbidden_iff (u d : ZMod N) :
    Forbidden (DeltaBTwoModelInterface.ModelSector (representation u) (representation d)) ↔
      charge u d ≠ 0 := by
  rw [forbidden_iff_not_allowed, allowed_iff]

def twoProbeEquiv (u d : ZMod N) (h : charge u d = 0) :
    DeltaBTwoModelInterface.ModelSector (representation u) (representation d) ≃ₗ[ℂ]
      (Fin 2 → ℂ) :=
  DeltaBTwoScalarSelection.twoProbeEquiv _ _ ((neutral_iff u d).mpr h)

theorem simultaneous_iff (c : CyclicResidualSelection.Charges N) :
    (Forbidden (DeltaLOneSignedFields.Sector (CyclicResidualSelection.flavor c) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation (c 3))) ∧
      Allowed (DeltaBTwoModelInterface.ModelSector (representation (c 1)) (representation (c 2)))) ↔
    ((∀ i : Fin 4, CyclicResidualSelection.familyCharge c i ≠ 0) ∧
      c 3+c 3=0 ∧ charge (c 1) (c 2)=0) := by
  rw [CyclicResidualSelection.forbidden_total_iff,
    CyclicResidualSelection.allowed_weinberg_iff, allowed_iff]

theorem simultaneous_forbidden_iff (c : CyclicResidualSelection.Charges N) :
    (Forbidden (DeltaLOneSignedFields.Sector (CyclicResidualSelection.flavor c) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation (c 3))) ∧
      Forbidden (DeltaBTwoModelInterface.ModelSector (representation (c 1)) (representation (c 2)))) ↔
    ((∀ i : Fin 4, CyclicResidualSelection.familyCharge c i ≠ 0) ∧
      c 3+c 3=0 ∧ charge (c 1) (c 2)≠0) := by
  rw [CyclicResidualSelection.forbidden_total_iff,
    CyclicResidualSelection.allowed_weinberg_iff, forbidden_iff]

theorem quarkParity_allowed :
    Allowed (DeltaBTwoModelInterface.ModelSector
      (representation (CyclicResidualSelection.quarkParity 1))
      (representation (CyclicResidualSelection.quarkParity 2))) := by
  rw [allowed_iff]
  decide +kernel

/-- Charges that forbid both specified baryon sectors, without a Yukawa premise. -/
def forbidBoth : CyclicResidualSelection.Charges 5 := ![1,1,0,0,0]

theorem forbidBoth_conditions :
    (∀ i : Fin 4, CyclicResidualSelection.familyCharge forbidBoth i ≠ 0) ∧
      forbidBoth 3+forbidBoth 3=0 ∧ charge (forbidBoth 1) (forbidBoth 2)≠0 := by
  constructor
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel

theorem forbidBoth_selection :
    Forbidden (DeltaLOneSignedFields.Sector (CyclicResidualSelection.flavor forbidBoth) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (representation (forbidBoth 3))) ∧
      Forbidden (DeltaBTwoModelInterface.ModelSector
        (representation (forbidBoth 1)) (representation (forbidBoth 2))) :=
  (simultaneous_forbidden_iff _).mpr forbidBoth_conditions

theorem trivial_allowed (N : ℕ) [NeZero N] :
    Allowed (DeltaBTwoModelInterface.ModelSector
      (representation (0 : ZMod N)) (representation (0 : ZMod N))) := by
  rw [allowed_iff]; simp [charge]

theorem order_one_allowed (u d : ZMod 1) :
    Allowed (DeltaBTwoModelInterface.ModelSector (representation u) (representation d)) := by
  rw [allowed_iff]; exact Subsingleton.elim _ _

end
end Physics.DeltaBTwoCyclicSelection
