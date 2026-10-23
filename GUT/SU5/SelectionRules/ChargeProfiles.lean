import Math.RepresentationTheory.Characters.UnitaryCharacterProfile
import Physics.StandardModel.Spectrum.Charges.FiniteChargeProfiles
import GUT.SU5.SelectionRules.SupportedFields

open Physics

open Math

/-!
# Actual retained SU(5) matter in the common charge-profile interface

Profiles count full residual eigenspaces of the generation action. Occupied
labels give the existing injective full-SM field maps, not just torus vectors.
-/

set_option autoImplicit false

namespace GUT.SU5.ChargeProfiles

noncomputable section

open MatterSource ResidualSectors SupportedFields FiniteChargeProfiles
open StandardBranchProtonObstruction FiniteAbelianChargeSectors

variable {H : Type*} [CommGroup H] {n : ℕ}

def kindProfile (R : OrdinaryAction H n) (i : Kind) : ChargeLabel H →₀ ℕ :=
  Finsupp.mapDomain Additive.ofMul
    (UnitaryCharacterProfile.profile (representation R i) (representation_unitary R i))

@[simp] theorem kindProfile_apply (R : OrdinaryAction H n) (i : Kind) (q : ChargeLabel H) :
    kindProfile R i q = Module.finrank ℂ (sector R i q.toMul).toSubmodule := by
  change kindProfile R i (Additive.ofMul q.toMul) = _
  rw [kindProfile, Finsupp.mapDomain_apply_of_injective Additive.ofMul.injective,
    UnitaryCharacterProfile.profile_apply]
  rfl

theorem kindProfile_total (R : OrdinaryAction H n) (i : Kind) : total (kindProfile R i) = n := by
  unfold total kindProfile
  rw [Finsupp.sum_mapDomain_index (by simp) (by simp)]
  simpa using UnitaryCharacterProfile.total_profile (representation R i) (representation_unitary R i)

def profiles (R : OrdinaryAction H n) : Profiles (ChargeLabel H) :=
  ⟨kindProfile R .ten, kindProfile R .ten, kindProfile R .barFive,
    kindProfile R .barFive, kindProfile R .ten⟩

theorem profiles_totals (R : OrdinaryAction H n) : HasCommonTotal (profiles R) n := by
  constructor <;> apply kindProfile_total

theorem profiles_compatible (R : OrdinaryAction H n) : OrbitCompatible (profiles R) :=
  ⟨rfl, rfl, rfl⟩

def family (R : OrdinaryAction H n) (hn : 0 < n) : Family (ChargeLabel H) :=
  ⟨profiles R, n, hn, profiles_totals R⟩

theorem mode_at_occupied (R : OrdinaryAction H n) (i : Kind) (q : ChargeLabel H)
    (hq : 0 < kindProfile R i q) : ∃ M : Mode R i, M.character = q.toMul := by
  have hp : 0 < UnitaryCharacterProfile.profile (representation R i)
      (representation_unitary R i) q.toMul := by
    rw [UnitaryCharacterProfile.profile_apply]
    rw [kindProfile_apply] at hq
    exact hq
  obtain ⟨v, hv, he⟩ := UnitaryCharacterProfile.exists_eigenvector_of_pos
    (representation R i) (representation_unitary R i) q.toMul hp
  exact ⟨⟨q.toMul, v, hv, he⟩, rfl⟩

theorem kindProfile_pos_of_mode {R : OrdinaryAction H n} {i : Kind} (M : Mode R i) :
    0 < kindProfile R i (Additive.ofMul M.character) := by
  rw [kindProfile_apply]
  have hp := UnitaryCharacterProfile.profile_pos_of_eigenvector
    (representation R i) (representation_unitary R i) M.character M.vector M.nonzero M.eigen
  rw [UnitaryCharacterProfile.profile_apply] at hp
  exact hp

/-- Any occupied choice has the old actual injective field intertwiners,
including choices with different charges inside a shared profile. -/
theorem support_of_occupied (R : OrdinaryAction H n) (k : Charges (ChargeLabel H))
    (hk : Occupied (profiles R) k) : Nonempty (Support R k) := by
  obtain ⟨Q, hQ⟩ := mode_at_occupied R .ten k.quark hk.1
  obtain ⟨U, hU⟩ := mode_at_occupied R .ten k.up hk.2.1
  obtain ⟨D, hD⟩ := mode_at_occupied R .barFive k.down hk.2.2.1
  obtain ⟨L, hL⟩ := mode_at_occupied R .barFive k.lepton hk.2.2.2.1
  obtain ⟨E, hE⟩ := mode_at_occupied R .ten k.electron hk.2.2.2.2
  exact ⟨⟨hQ ▸ quarkField Q, hU ▸ upField U, hE ▸ electronField E,
    hD ▸ downField D, hL ▸ leptonField L⟩⟩

theorem supported_profile_tensors (R : OrdinaryAction H n) (hn : 0 < n) :
    ∃ k : Charges (ChargeLabel H), Occupied (profiles R) k ∧ Nonempty (Support R k) ∧
      StandardSMGaugeTensor.qque ≠ 0 ∧ StandardSMGaugeTensor.duql ≠ 0 ∧
      (∀ g x, StandardSMGaugeTensor.qque (StandardSMResidualTensor.qqueRepresentation k g x) =
        StandardSMGaugeTensor.qque x) ∧
      (∀ g x, StandardSMGaugeTensor.duql (StandardSMResidualTensor.duqlRepresentation k g x) =
        StandardSMGaugeTensor.duql x) := by
  obtain ⟨k, hk, hc⟩ := exists_occupied_compatible (family R hn) (profiles_compatible R)
  exact ⟨k, hk, support_of_occupied R k hk,
    StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible k hc⟩

end

end GUT.SU5.ChargeProfiles
