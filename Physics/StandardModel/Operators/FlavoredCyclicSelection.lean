import Physics.StandardModel.Operators.FlavoredCyclicCoordinates
import Physics.StandardModel.Operators.QqqlDiagonalCoordinates
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness

open Math

/-! Finite generation-dependent cyclic selection for the full signed,
derivative-free dimension-six four-fermion sector and residual-neutral LLHH. -/
namespace GUT.FlavoredCyclicSelection
set_option autoImplicit false
noncomputable section
open CyclicWeightCoordinates FlavoredCyclicCoordinates SelectionCriteria
universe u
variable {N : ℕ} [NeZero N]
  (I : Fin 5 → Type u) [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
  (c : ∀ s, I s → ZMod N)

def slot (s : Fin 10) : Fin 5 := ⟨s.val % 5, Nat.mod_lt _ (by decide)⟩
abbrev signedIndex (s : Fin 10) := I (slot s)
def signedCharge (s : Fin 10) (i : signedIndex I s) : ZMod N :=
  if s.val < 5 then c (slot s) i else -c (slot s) i
def flavor (s : Fin 10) := diagonal (signedCharge I c s)

omit [NeZero N] [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)] in
theorem opposite_charge (s : Fin 10) (h : 5 ≤ s.val) (i : signedIndex I s) :
    signedCharge I c s i = -c (slot s) i := by
  simp [signedCharge, show ¬s.val < 5 by omega]

theorem opposite_slot (s : Fin 5) : slot ⟨s.val+5, by omega⟩ = s := by
  apply Fin.ext
  simp [slot, Nat.mod_eq_of_lt s.isLt]

abbrev DuqlIndex := {p // fourCharge (c 2) (c 1) (c 0) (c 3) p = 0}
abbrev QqueIndex := {p // qqueCharge (c 0) (c 1) (c 4) p = 0}
abbrev QqqlIndex := {p // QqqlDiagonalCoordinates.charge
  (c 0 ∘ (Fintype.equivFin (I 0)).symm)
  (c 3 ∘ (Fintype.equivFin (I 3)).symm) p = 0}
abbrev DuueIndex := {p // fourCharge (c 1) (c 1) (c 2) (c 4) p = 0}
abbrev Coordinates := (DuqlIndex I c → ℂ) × ((QqueIndex I c → ℂ) ×
  ((QqqlIndex I c → ℂ) × (DuueIndex I c → ℂ)))

def duqlResidualEquiv :=
  (DuqlExteriorCompleteness.homEquiv (diagonal (c 2)) (diagonal (c 1))
    (diagonal (c 0)) (diagonal (c 3))).symm.trans
      (duqlEquiv (c 2) (c 1) (c 0) (c 3))
def qqueResidualEquiv :=
  (QquePhysicalExteriorCompleteness.exteriorEquiv (diagonal (c 0))
    (diagonal (c 1)) (diagonal (c 4))).symm.trans (qqueEquiv (c 0) (c 1) (c 4))
def qqqlResidualEquiv :=
  (QqqlExteriorCompleteness.exteriorEquiv (diagonal (c 0)) (diagonal (c 3))).symm.trans
    (QqqlDiagonalCoordinates.diagonalEquiv (c 0) (c 3))
def duueResidualEquiv :=
  (DuueResidualCompleteness.homEquiv (diagonal (c 1)) (diagonal (c 2))
    (diagonal (c 4))).symm.trans (duueEquiv (c 1) (c 2) (c 4))

/-- The physical input is the full signed exterior sector, not a chosen family. -/
def equiv : DeltaLOneSignedFields.Sector (flavor I c) 1 ≃ₗ[ℂ] Coordinates I c :=
  (DeltaLOneCoefficientCompleteness.equiv (flavor I c)).trans
    (LinearEquiv.prodCongr (duqlResidualEquiv I c)
      (LinearEquiv.prodCongr (qqueResidualEquiv I c)
        (LinearEquiv.prodCongr (qqqlResidualEquiv I c) (duueResidualEquiv I c))))

@[simp] theorem reconstruct_extract (f : DeltaLOneSignedFields.Sector (flavor I c) 1) :
    (equiv I c).symm (equiv I c f) = f := (equiv I c).symm_apply_apply f
@[simp] theorem extract_reconstruct (d : Coordinates I c) :
    equiv I c ((equiv I c).symm d) = d := (equiv I c).apply_symm_apply d

theorem finrank_total : Module.finrank ℂ (DeltaLOneSignedFields.Sector (flavor I c) 1) =
    Fintype.card (DuqlIndex I c) + (Fintype.card (QqueIndex I c) +
      (Fintype.card (QqqlIndex I c) + Fintype.card (DuueIndex I c))) := by
  rw [(equiv I c).finrank_eq]
  simp only [Coordinates, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

theorem forbidden_function {A : Type*} : Forbidden (A → ℂ) ↔ IsEmpty A := by
  constructor
  · intro h
    constructor
    intro a
    have he := congrFun (h (fun _ => 1)) a
    simp at he
  · intro h f
    funext a
    exact isEmptyElim a

theorem allowed_function {A : Type*} : Allowed (A → ℂ) ↔ Nonempty A := by
  rw [← not_iff_not, ← forbidden_iff_not_allowed, forbidden_function]
  simp only [not_nonempty_iff]

theorem forbidden_total_iff : Forbidden (DeltaLOneSignedFields.Sector (flavor I c) 1) ↔
    IsEmpty (DuqlIndex I c) ∧ (IsEmpty (QqueIndex I c) ∧
      (IsEmpty (QqqlIndex I c) ∧ IsEmpty (DuueIndex I c))) := by
  rw [(ofEquiv (equiv I c)).forbidden]
  simp only [Coordinates, forbidden_prod, forbidden_function]

theorem allowed_total_iff : Allowed (DeltaLOneSignedFields.Sector (flavor I c) 1) ↔
    Nonempty (DuqlIndex I c) ∨ Nonempty (QqueIndex I c) ∨
      Nonempty (QqqlIndex I c) ∨ Nonempty (DuueIndex I c) := by
  rw [← not_iff_not, ← forbidden_iff_not_allowed, forbidden_total_iff]
  simp only [not_or, not_nonempty_iff]

theorem simultaneous_iff :
    (Forbidden (DeltaLOneSignedFields.Sector (flavor I c) 1) ∧
      Allowed (WeinbergSMInterface.ModelSector (diagonal (c 3)))) ↔
    (IsEmpty (DuqlIndex I c) ∧ (IsEmpty (QqueIndex I c) ∧
      (IsEmpty (QqqlIndex I c) ∧ IsEmpty (DuueIndex I c)))) ∧
      ∃ s, symmetricCharge 2 (c 3) s = 0 := by
  rw [forbidden_total_iff, llhh_allowed]

end
end GUT.FlavoredCyclicSelection
