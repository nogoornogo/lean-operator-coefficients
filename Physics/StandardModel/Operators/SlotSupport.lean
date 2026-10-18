import Physics.StandardModel.Operators.StandardModelLocalOperator

open Math

/-! Operator-local support, without requiring unused spectator species.
The original full-five-species support predicates remain unchanged. -/

set_option autoImplicit false
namespace GUT.StandardModelSlotSupport
noncomputable section

open StandardModelLocalOperator StandardAbelianCharge
open StandardBranchProtonObstruction FiniteAbelianChargeSectors

variable {A : Type*}

/-- Right-handed slots use the support of their left-chiral conjugate sector;
the charge inversion itself is already part of `operatorCharacter`. -/
def FieldSupported (p : ResolvedCharacter A) (k : Charges A) : PhysicalFermion → Prop
  | .quarkDoublet => quarkProfile p k.quark ≠ 0
  | .upRight => upProfile p k.up ≠ 0
  | .downRight => downProfile p k.down ≠ 0
  | .leptonDoublet => leptonProfile p k.lepton ≠ 0
  | .electronRight => electronProfile p k.electron ≠ 0

def SlotsSupported (p : ResolvedCharacter A) (k : Charges A)
    (O : FourFermionOperator) : Prop := ∀ i, FieldSupported p k (O i)

theorem slotsSupported_of_chargesSupported {p : ResolvedCharacter A} {k : Charges A}
    (h : ChargesSupported p k) (O : FourFermionOperator) : SlotsSupported p k O := by
  intro i
  rcases h with ⟨hq, hu, hd, hl, he⟩
  cases O i <;> assumption

theorem qque_slotsSupported_iff (p : ResolvedCharacter A) (k : Charges A) :
    SlotsSupported p k qqueOperator ↔
      quarkProfile p k.quark ≠ 0 ∧ upProfile p k.up ≠ 0 ∧ electronProfile p k.electron ≠ 0 := by
  constructor
  · intro h
    exact ⟨h 0, h 2, h 3⟩
  · rintro ⟨hq, hu, he⟩ i
    fin_cases i <;> assumption

variable {H : Type*} [CommGroup H]

def ForbidsEverySlotSupportedPhysicalDeltaBOneOperator
    (p : ResolvedCharacter (ChargeLabel H)) : Prop :=
  ∀ k : Charges (ChargeLabel H), ∀ O : FourFermionOperator,
    SlotsSupported p k O → IsPhysicalDeltaBOneOperator O → operatorCharacter k O ≠ 1

theorem slotwise_prohibition_implies_legacy {p : ResolvedCharacter (ChargeLabel H)}
    (h : ForbidsEverySlotSupportedPhysicalDeltaBOneOperator p) :
    ForbidsEverySupportedPhysicalDeltaBOneOperator p := by
  intro k hk O hO
  exact h k O (slotsSupported_of_chargesSupported hk O) hO

theorem not_slotwise_prohibition_of_qque {p : ResolvedCharacter (ChargeLabel H)}
    (k : Charges (ChargeLabel H)) (hs : SlotsSupported p k qqueOperator)
    (hn : protonFirstCharacter k = 1) :
    ¬ ForbidsEverySlotSupportedPhysicalDeltaBOneOperator p := by
  intro h
  exact h k qqueOperator hs qque_isPhysicalDeltaBOneOperator
    ((qque_operatorCharacter k).trans hn)

/-- A control for the legacy interface: absence of an unused spectator
species makes its universal prohibition vacuous. -/
theorem legacy_prohibition_of_no_lepton (p : ResolvedCharacter (ChargeLabel H))
    (h : ∀ q, leptonProfile p q = 0) : ForbidsEverySupportedPhysicalDeltaBOneOperator p := by
  intro k hk
  exact False.elim (hk.2.2.2.1 (h k.lepton))

end
end GUT.StandardModelSlotSupport
