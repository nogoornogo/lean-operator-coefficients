import Math.RepresentationTheory.ProhibitionInput
import Physics.StandardModel.Operators.KorenSMSelection
import Physics.StandardModel.Operators.BgwZ6Selection
import Physics.StandardModel.Operators.DgtFlavorRestriction
import Physics.StandardModel.Operators.QuarticityAdapters
import Physics.StandardModel.Operators.WeinbergSMInterface

namespace GUT.ProhibitionInputSM
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput SelectionCriteria
variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))


abbrev Forbids (t : ℤ × ℤ → Prop) (n m : ℕ) : Prop :=
  Forbidden (ComposableBLSupport.Input flavor scalarFlavor t n m)
abbrev AllForbids (t : ℤ × ℤ → Prop) : Prop := ∀ n m, Forbids flavor scalarFlavor t n m

theorem facade_iff (t : ℤ × ℤ → Prop) (n m : ℕ) :
    Forbids flavor scalarFlavor t n m ↔ ProhibitionInput.Forbids
      DeltaLOneSignedFields.localField GradedBnvComparison.scalarLocal flavor scalarFlavor
      (ComposableBLSupport.specification t) n m :=
  (SelectionCriteria.ofEquiv (ComposableBLSupport.inputEquiv flavor scalarFlavor t n m)).forbidden

theorem residual_iff (t : ℤ × ℤ → Prop) (n m : ℕ) :
    Forbids flavor scalarFlavor t n m ↔
      Forbidden (ComposableBLSupport.Residual flavor scalarFlavor t n m) :=
  (SelectionCriteria.ofEquiv (ComposableBLSupport.equiv flavor scalarFlavor t n m)).forbidden

theorem koren : AllForbids (KorenSMSelection.flavor (F := F))
    (KorenSMSelection.scalarFlavor (S := S)) KorenSMSelection.target :=
  KorenSMSelection.all_forbidden

theorem bgw : AllForbids (BgwZ6Selection.flavor (F := F))
    (BgwZ6Selection.scalarFlavor (S := S)) ComposableBLSupport.bOneTwo :=
  BgwZ6Selection.all_forbidden

theorem dgt : AllForbids DgtFlavorRestriction.irFlavor DgtFlavorRestriction.irScalar
    ComposableBLSupport.bOneTwo := DgtFlavorRestriction.all_bnv_forbidden

theorem dgt_restriction : ¬ Function.Surjective DgtFlavorRestriction.restrictMap :=
  DgtFlavorRestriction.restriction_not_surjective

/-- Different alphabets: SM/Higgs L2 vanishes while the dressed nuR/eta sector survives. -/
theorem quarticity_domains :
    AllForbids QuarticityAdapters.smFlavor QuarticityAdapters.smScalar
      (fun q => q.2.natAbs = 2) ∧ Allowed QuarticityAdapters.Dressed :=
  ⟨QuarticityAdapters.sm_lTwo_forbidden, QuarticityAdapters.exists_dressed⟩

/-- Actual one-copy LLHH coefficient domain, with neutral Higgs flavor. -/
theorem llhh_forbidden_iff (a : Representation ℂ R ℂ) :
    Forbidden (WeinbergSMInterface.ModelSector a) ↔ ∃ g, (a g 1) ^ 2 ≠ 1 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed]
  rw [SelectionCriteria.allowed_equiv (WeinbergSMInterface.coefficientEquiv a),
    Allowed, WeinbergScalarFlavor.exists_nonzero_iff_square_trivial]
  simp only [not_forall]
end
end GUT.ProhibitionInputSM
