import Physics.StandardModel.Operators.InverseCyclicSMCharges
import Physics.StandardModel.Operators.DeltaBTwoCyclicSelection

namespace GUT.InverseCyclicSectorProperties
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria CyclicCharge
variable {k : ℕ} [NeZero k]

theorem six_quark_forbidden_iff (q : ZMod k) :
    Forbidden (DeltaBTwoModelInterface.ModelSector (representation q) (representation q)) ↔ 6*q ≠ 0 := by
  rw [DeltaBTwoCyclicSelection.forbidden_iff]
  have he : DeltaBTwoCyclicSelection.charge q q = 6*q := by unfold DeltaBTwoCyclicSelection.charge; ring
  rw [he]

theorem llhh_forbidden_iff (l : ZMod k) :
    Forbidden (WeinbergSMInterface.ModelSector (representation l)) ↔ 2*l ≠ 0 := by
  rw [forbidden_iff_not_allowed,CyclicResidualSelection.allowed_weinberg_iff]
  have he : l+l=2*l := by ring
  rw [he]

theorem six_quark_allowed_iff (q : ZMod k) :
    Allowed (DeltaBTwoModelInterface.ModelSector (representation q) (representation q)) ↔ 6*q = 0 := by
  rw [DeltaBTwoCyclicSelection.allowed_iff]
  have he : DeltaBTwoCyclicSelection.charge q q = 6*q := by unfold DeltaBTwoCyclicSelection.charge; ring
  rw [he]

theorem llhh_allowed_iff (l : ZMod k) :
    Allowed (WeinbergSMInterface.ModelSector (representation l)) ↔ 2*l = 0 := by
  rw [CyclicResidualSelection.allowed_weinberg_iff]
  have he : l+l=2*l := by ring
  rw [he]

/-- Counts classify labeled assignments and specified one-copy domains only. -/
def profileCount (k : ℕ) (b l : Bool) : ℕ :=
  ((InverseCyclicSMCharges.candidates k).filter (fun x =>
    decide (6*x.1 ≠ 0) = b ∧ decide (2*x.2 ≠ 0) = l)).card

theorem profile_counts :
    (∑ i : Fin 11, profileCount (i.val+2) false false) = 20 ∧
    (∑ i : Fin 11, profileCount (i.val+2) false true) = 166 ∧
    (∑ i : Fin 11, profileCount (i.val+2) true false) = 70 ∧
    (∑ i : Fin 11, profileCount (i.val+2) true true) = 316 := by
  decide +kernel
end
end GUT.InverseCyclicSectorProperties
