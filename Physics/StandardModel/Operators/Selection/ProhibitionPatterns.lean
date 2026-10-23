import Physics.StandardModel.Operators.Selection.ProhibitionInputSM
import Math.RepresentationTheory.Protection.ProhibitionPatterns

namespace Physics.ProhibitionPatterns
set_option autoImplicit false
noncomputable section
open Math Representation ProhibitionSpecification DeltaLOneSignedInput

inductive BLTarget where
  | bOne | bTwo | lTwo
  deriving DecidableEq

def target : BLTarget → ℤ × ℤ → Prop
  | .bOne => fun q => q.1.natAbs = 3
  | .bTwo => fun q => q.1.natAbs = 6
  | .lTwo => fun q => q.2.natAbs = 2

def specification (t : BLTarget) : Spec Species BnvMixedInput.ScalarSpecies :=
  ComposableBLSupport.specification (target t)

def request (chosen : Set BLTarget) : Spec Species BnvMixedInput.ScalarSpecies :=
  iUnion (fun t : chosen => specification t.val)

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))



abbrev ForbidsChosen (chosen : Set BLTarget) : Prop :=
  ProhibitionInput.AllForbids DeltaLOneSignedFields.localField
    GradedBnvComparison.scalarLocal flavor scalarFlavor (request chosen)

theorem chosen_iff (chosen : Set BLTarget) :
    ForbidsChosen flavor scalarFlavor chosen ↔
      ∀ t ∈ chosen, ProhibitionInputSM.AllForbids flavor scalarFlavor (target t) := by
  unfold ForbidsChosen request
  rw [ProhibitionInput.all_iUnion_iff]
  constructor
  · intro h t ht n m
    exact (ProhibitionInputSM.facade_iff flavor scalarFlavor (target t) n m).mpr
      (h ⟨t, ht⟩ n m)
  · intro h t n m
    exact (ProhibitionInputSM.facade_iff flavor scalarFlavor (target t.val) n m).mp
      (h t.val t.property n m)

theorem triple_iff : ForbidsChosen flavor scalarFlavor Set.univ ↔
    ProhibitionInputSM.AllForbids flavor scalarFlavor (target .bOne) ∧
    ProhibitionInputSM.AllForbids flavor scalarFlavor (target .bTwo) ∧
    ProhibitionInputSM.AllForbids flavor scalarFlavor (target .lTwo) := by
  rw [chosen_iff]
  constructor
  · intro h; exact ⟨h .bOne (Set.mem_univ _), h .bTwo (Set.mem_univ _), h .lTwo (Set.mem_univ _)⟩
  · rintro ⟨h1,h2,h3⟩ t _; cases t <;> assumption

theorem empty_chosen : ForbidsChosen flavor scalarFlavor ∅ := by
  rw [chosen_iff]
  intro t ht; cases ht

/-- Mixed B/L support and dipole selectors retain their respective admitted domains. -/
def JointForbids {H A B I : Type*} [Group H]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (chosen : Set BLTarget)
    (a : Representation ℂ H A) (b : Representation ℂ H B)
    (mu : I → A) (electron : I → Module.Dual ℂ B) : Prop :=
  ForbidsChosen flavor scalarFlavor chosen ∧
    ComposableDipoleSelection.selector a b mu electron = 0

theorem joint_iff {H A B I : Type*} [Group H]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (chosen : Set BLTarget)
    (a : Representation ℂ H A) (b : Representation ℂ H B)
    (mu : I → A) (electron : I → Module.Dual ℂ B) :
    JointForbids flavor scalarFlavor chosen a b mu electron ↔
      (∀ t ∈ chosen, ProhibitionInputSM.AllForbids flavor scalarFlavor (target t)) ∧
      (∀ i, DipoleFlavorSelection.residualSelector a b (mu i) (electron i) = 0) := by
  unfold JointForbids
  rw [chosen_iff, ComposableDipoleSelection.forbidden_iff]

/-- Any subset of the three targets is forbidden by the existing Koren certificate. -/
theorem koren_chosen (chosen : Set BLTarget) :
    ForbidsChosen (KorenSMSelection.flavor (F := F))
      (KorenSMSelection.scalarFlavor (S := S)) chosen := by
  rw [chosen_iff]
  intro t _ n m
  apply (ProhibitionInputSM.facade_iff _ _ (target t) n m).mpr
  apply ProhibitionInput.mono _ _ _ _ (specification t)
    (ComposableBLSupport.specification KorenSMSelection.target) n m
  · intro p s ht
    change target t _ at ht
    change KorenSMSelection.target _
    cases t <;> simp only [target] at ht <;> simp [KorenSMSelection.target, ht]
  · exact (ProhibitionInputSM.facade_iff _ _ KorenSMSelection.target n m).mp
      (KorenSMSelection.all_forbidden n m)

def baryonTargets : Set BLTarget := {t | t ≠ .lTwo}

theorem bgw_baryon : ForbidsChosen (BgwZ6Selection.flavor (F := F))
    (BgwZ6Selection.scalarFlavor (S := S)) baryonTargets := by
  rw [chosen_iff]
  intro t ht n m
  apply (ProhibitionInputSM.facade_iff _ _ (target t) n m).mpr
  apply ProhibitionInput.mono _ _ _ _ (specification t)
    (ComposableBLSupport.specification ComposableBLSupport.bOneTwo) n m
  · intro p s hp
    change target t _ at hp
    change ComposableBLSupport.bOneTwo _
    cases t with
    | bOne => exact Or.inl hp
    | bTwo => exact Or.inr hp
    | lTwo => exact (ht rfl).elim
  · exact (ProhibitionInputSM.facade_iff _ _ _ n m).mp (BgwZ6Selection.all_forbidden n m)

/-- Residual baryon prohibition also forbids coefficients for the larger UV action. -/
theorem dgt_uv_baryon : ForbidsChosen DgtFlavorRestriction.uvFlavor
    DgtFlavorRestriction.uvScalar baryonTargets := by
  have h : ProhibitionInput.AllForbids DeltaLOneSignedFields.localField
      GradedBnvComparison.scalarLocal DgtFlavorRestriction.uvFlavor
      DgtFlavorRestriction.uvScalar
      (ComposableBLSupport.specification ComposableBLSupport.bOneTwo) := by
    intro n m f
    classical
    let r := GradedCompletenessRestriction.selectedMap DeltaLOneSignedFields.localField
      GradedBnvComparison.scalarLocal DgtFlavorRestriction.uvFlavor
      DgtFlavorRestriction.uvScalar DgtFlavorRestriction.embedding n m
      ((ComposableBLSupport.specification ComposableBLSupport.bOneTwo).test n m)
    have hi : ProhibitionInput.Forbids DeltaLOneSignedFields.localField
        GradedBnvComparison.scalarLocal
        (fun u => (DgtFlavorRestriction.uvFlavor u).comp DgtFlavorRestriction.embedding)
        (fun u => (DgtFlavorRestriction.uvScalar u).comp DgtFlavorRestriction.embedding)
        (ComposableBLSupport.specification ComposableBLSupport.bOneTwo) n m := by
      simp only [DgtFlavorRestriction.flavor_restriction, DgtFlavorRestriction.scalar_restriction]
      exact (ProhibitionInputSM.facade_iff _ _ _ n m).mp
        (DgtFlavorRestriction.all_bnv_forbidden n m)
    have hz := hi (r f)
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact congrArg (fun q => q.val.toLinearMap) hz
  rw [chosen_iff]
  intro t ht n m
  apply (ProhibitionInputSM.facade_iff _ _ (target t) n m).mpr
  apply ProhibitionInput.mono _ _ _ _ (specification t)
    (ComposableBLSupport.specification ComposableBLSupport.bOneTwo) n m
  · intro p s hp
    change target t _ at hp
    change ComposableBLSupport.bOneTwo _
    cases t with
    | bOne => exact Or.inl hp
    | bTwo => exact Or.inr hp
    | lTwo => exact (ht rfl).elim
  · exact h n m

/-- Same UV residual group: B1/B2 prohibition plus two prescribed dipole transitions. -/
theorem dgt_joint : JointForbids DgtFlavorRestriction.uvFlavor
    DgtFlavorRestriction.uvScalar baryonTargets
    DgtFlavorRestriction.leptonUV DgtFlavorRestriction.leptonUV
    (fun _ : Fin 2 => DgtFlavorRestriction.mu) DgtFlavorRestriction.targetCovector :=
  ⟨dgt_uv_baryon, DgtFlavorRestriction.uv_dipoles_forbidden⟩

end
end Physics.ProhibitionPatterns
