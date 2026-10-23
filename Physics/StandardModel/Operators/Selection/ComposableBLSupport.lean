import Physics.StandardModel.Operators.BaryonOne.Inputs.GradedBnvComparison
import Math.RepresentationTheory.Protection.ComposableProtection

/-! One admitted SM/Higgs field input, with replaceable B/L target predicates. -/
namespace Physics.ComposableBLSupport
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
noncomputable section
open Math Representation DeltaLOneSignedInput
open ProhibitionSpecification
open scoped BigOperators

def fermionCharge (u : Species) : ℤ × ℤ := (baryon u, lepton u)
def bosonCharge (_ : BnvMixedInput.ScalarSpecies) : ℤ × ℤ := (0,0)
def specification (t : ℤ × ℤ → Prop) : Spec Species BnvMixedInput.ScalarSpecies :=
  charges fermionCharge bosonCharge t

def bOneTwo (q : ℤ × ℤ) : Prop := q.1.natAbs = 3 ∨ q.1.natAbs = 6
def bOneOrLTwo (q : ℤ × ℤ) : Prop := q.1.natAbs = 3 ∨ q.2.natAbs = 2

theorem charge_eq {n m : ℕ} (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies) :
    MixedChargeSelection.charge fermionCharge bosonCharge p s =
      (∑ i, baryon (p i), ∑ i, lepton (p i)) := by
  ext <;> simp [MixedChargeSelection.charge, fermionCharge, bosonCharge, Prod.fst_sum, Prod.snd_sum]

theorem old_support {n m : ℕ} (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies) :
    (specification (fun q => q.1 ≠ 0)).test n m p s ↔ GradedBnvComparison.allowed p s := by
  change (MixedChargeSelection.charge fermionCharge bosonCharge p s).1 ≠ 0 ↔ _
  rw [charge_eq]; rfl

theorem bOne_or_lTwo : specification bOneOrLTwo =
    union (specification (fun q => q.1.natAbs = 3))
      (specification (fun q => q.2.natAbs = 2)) := rfl

theorem bOne_or_bTwo : specification bOneTwo =
    union (specification (fun q => q.1.natAbs = 3))
      (specification (fun q => q.1.natAbs = 6)) := rfl

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))

/-- Coefficients on the existing actual field actions, with a replaceable target. -/
abbrev Input (t : ℤ × ℤ → Prop) (n m : ℕ) :=
  MixedSpeciesProjection.supportSpace ((specification t).test n m)
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)

def inputEquiv (t : ℤ × ℤ → Prop) (n m : ℕ) :
    Input flavor scalarFlavor t n m ≃ₗ[ℂ]
      MixedSpeciesProjection.supportSpace ((specification t).test n m)
        (GradedBnvComparison.fermion flavor) (GradedBnvComparison.boson scalarFlavor) := by
  unfold Input
  rw [GradedBnvComparison.fermion_eq, GradedBnvComparison.boson_eq]

abbrev Residual (t : ℤ × ℤ → Prop) (n m : ℕ) :=
  ∀ x : MixedContentOrbits.Selected ((specification t).test n m),
    GradedMixedCompleteness.Factor DeltaLOneSignedFields.localField
      GradedBnvComparison.scalarLocal flavor scalarFlavor n m x.val

irreducible_def equiv (t : ℤ × ℤ → Prop) (n m : ℕ) :
    Input flavor scalarFlavor t n m ≃ₗ[ℂ] Residual flavor scalarFlavor t n m := by
  classical
  exact (inputEquiv flavor scalarFlavor t n m).trans
    (GradedMixedCompleteness.selectedEquiv DeltaLOneSignedFields.localField
      GradedBnvComparison.scalarLocal flavor scalarFlavor n m
      ((specification t).test n m) ((specification t).stable n m))

theorem reconstruct_extract (t : ℤ × ℤ → Prop) (n m : ℕ)
    (f : Input flavor scalarFlavor t n m) :
    (equiv flavor scalarFlavor t n m).symm (equiv flavor scalarFlavor t n m f) = f :=
  LinearEquiv.symm_apply_apply _ _

theorem extract_reconstruct (t : ℤ × ℤ → Prop) (n m : ℕ)
    (q : Residual flavor scalarFlavor t n m) : equiv flavor scalarFlavor t n m ((equiv flavor scalarFlavor t n m).symm q) = q :=
  LinearEquiv.apply_symm_apply _ _

theorem union_forbidden_iff (s t : ℤ × ℤ → Prop) (n m : ℕ) :
    (∀ f : Input flavor scalarFlavor (fun q => s q ∨ t q) n m, f = 0) ↔
    (∀ f : Input flavor scalarFlavor s n m, f = 0) ∧
    (∀ f : Input flavor scalarFlavor t n m, f = 0) := by
  unfold Input
  rw [← GradedBnvComparison.fermion_eq flavor, ← GradedBnvComparison.boson_eq scalarFlavor]
  exact ComposableProtection.forbidden_union_iff DeltaLOneSignedFields.localField
    GradedBnvComparison.scalarLocal flavor scalarFlavor (specification s) (specification t) n m

theorem all_union_forbidden_iff (s t : ℤ × ℤ → Prop) :
    (∀ n m, ∀ f : Input flavor scalarFlavor (fun q => s q ∨ t q) n m, f = 0) ↔
    (∀ n m, ∀ f : Input flavor scalarFlavor s n m, f = 0) ∧
    (∀ n m, ∀ f : Input flavor scalarFlavor t n m, f = 0) := by
  simp only [union_forbidden_iff, forall_and]

theorem forbidden (t : ℤ × ℤ → Prop) (chi : R → AddChar (ℤ × ℤ) ℂ)
    (hf : ∀ g u v, flavor u g v = chi g (fermionCharge u) • v)
    (hb : ∀ g u v, scalarFlavor u g v = chi g (bosonCharge u) • v)
    (detect : ∀ n m (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies),
      t (MixedChargeSelection.charge fermionCharge bosonCharge p s) →
      ∃ g, chi g (MixedChargeSelection.charge fermionCharge bosonCharge p s) ≠ 1) :
    ∀ n m, ∀ f : Input flavor scalarFlavor t n m, f = 0 := by
  have h := ComposableProtection.charges_forbidden DeltaLOneSignedFields.localField
    GradedBnvComparison.scalarLocal flavor scalarFlavor fermionCharge bosonCharge
    chi hf hb t detect
  unfold Input
  rw [← GradedBnvComparison.fermion_eq flavor, ← GradedBnvComparison.boson_eq scalarFlavor]
  exact h
end
end Physics.ComposableBLSupport
