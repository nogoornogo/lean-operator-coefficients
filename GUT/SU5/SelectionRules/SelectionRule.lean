import GUT.SU5.SelectionRules.SupportedQuotient

open Math

/-!
# Scoped SU(5) ordinary-Abelian selection-rule obstruction

The retained matter is n(10 + bar5), n > 0. The only residual-action input
is an arbitrary unitary Abelian action commuting with the full SU(5) action.
Support is an actual equivariant injection, not a virtual coefficient.

This rules out universal charge prohibition in the declared dimension-six
signature class. Nonzero ordered internal tensors are provided separately;
no nonzero Wilson coefficient, Grassmann operator, or amplitude is asserted.
-/

set_option autoImplicit false

namespace GUT.SU5.SelectionRule

noncomputable section

open MatterSource SupportedFields SupportedTensors SupportedQuotient
open StandardSMGaugeTensor StandardModelLocalOperator
open FiniteAbelianChargeSectors StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H] {n : ℕ}

/-- Right-handed operator slots are supported by the duals of the indicated
left-handed conjugate fields, as proved by `SupportedTensors.rightSplit`. -/
def FieldSupported (R : OrdinaryAction H n) (k : Charges (ChargeLabel H)) :
    PhysicalFermion → Prop
  | .quarkDoublet => Nonempty (Realization R quark k.quark.toMul)
  | .upRight => Nonempty (Realization R upRight.dual k.up.toMul)
  | .downRight => Nonempty (Realization R downRight.dual k.down.toMul)
  | .leptonDoublet => Nonempty (Realization R lepton k.lepton.toMul)
  | .electronRight => Nonempty (Realization R electronRight.dual k.electron.toMul)

def OperatorSupported (R : OrdinaryAction H n) (k : Charges (ChargeLabel H))
    (O : FourFermionOperator) : Prop := ∀ s, FieldSupported R k (O s)

/-- Independent charge-sector choices at each slot. Only the component
selected by `O s` is used from the charge tuple at slot `s`. -/
def SlotsSupported (R : OrdinaryAction H n) (ks : Fin 4 → Charges (ChargeLabel H))
    (O : FourFermionOperator) : Prop := ∀ s, FieldSupported R (ks s) (O s)

def slotCharacter (ks : Fin 4 → Charges (ChargeLabel H)) (O : FourFermionOperator) : H →* Circle :=
  (∑ s, physicalCharge (ks s) (O s)).toMul

@[simp] theorem slotCharacter_const (k : Charges (ChargeLabel H)) (O : FourFermionOperator) :
    slotCharacter (fun _ => k) O = operatorCharacter k O := rfl

/-- Charge prohibition only; it is not a predicate on physical amplitudes.
No compatibility within a UV multiplet or equality between repeated field
slots is imposed on the quantified charges. -/
def ForbidsEverySupportedDeltaBOne (R : OrdinaryAction H n) : Prop :=
  ∀ (ks : Fin 4 → Charges (ChargeLabel H)) (O : FourFermionOperator),
    IsPhysicalDeltaBOneOperator O → SlotsSupported R ks O → slotCharacter ks O ≠ 1

theorem support_fields {R : OrdinaryAction H n} {k : Charges (ChargeLabel H)}
    (S : Support R k) (f : PhysicalFermion) : FieldSupported R k f := by
  cases f
  · exact ⟨S.quark⟩
  · exact ⟨S.up⟩
  · exact ⟨S.down⟩
  · exact ⟨S.lepton⟩
  · exact ⟨S.electron⟩

theorem support_operator {R : OrdinaryAction H n} {k : Charges (ChargeLabel H)}
    (S : Support R k) (O : FourFermionOperator) : OperatorSupported R k O :=
  fun s => support_fields S (O s)

/-- Output of the source theorem, never a hypothesis of the matter model.
Both forms live on actual field ranges and their contragredients. -/
structure OperatorWitness (R : OrdinaryAction H n) where
  charges : Charges (ChargeLabel H)
  fields : Support R charges
  qque_neutral : operatorCharacter charges qqueOperator = 1
  duql_neutral : operatorCharacter charges duqlOperator = 1
  qque_nonzero : qqueTensor fields ≠ 0
  duql_nonzero : duqlTensor fields ≠ 0
  qque_invariant : ∀ g x, qqueTensor fields (quotientQQueAction fields g x) = qqueTensor fields x
  duql_invariant : ∀ g x, duqlTensor fields (quotientDuqlAction fields g x) = duqlTensor fields x

theorem witness_exists (R : OrdinaryAction H n) (hn : 0 < n) : Nonempty (OperatorWitness R) := by
  obtain ⟨k, ⟨S⟩, hk⟩ := exists_supported_compatible R hn
  obtain ⟨h1, h2⟩ := protonCharacters_eq_one_of_su5OrbitCompatible k hk
  exact ⟨{
    charges := k
    fields := S
    qque_neutral := (qque_operatorCharacter k).trans h1
    duql_neutral := (duql_operatorCharacter k).trans h2
    qque_nonzero := qqueTensor_nonzero S
    duql_nonzero := duqlTensor_nonzero S
    qque_invariant := qque_quotient_invariant S hk
    duql_invariant := duql_quotient_invariant S hk }⟩

theorem OperatorWitness.not_forbids {R : OrdinaryAction H n} (W : OperatorWitness R) :
    ¬ ForbidsEverySupportedDeltaBOne R := by
  intro h
  exact h (fun _ => W.charges) qqueOperator qque_isPhysicalDeltaBOneOperator
    (support_operator W.fields qqueOperator) W.qque_neutral

/-- The finite-generation endpoint, with no equal-charge, support, or
nonzero-channel assumption. The quotient-group tensor witnesses are output. -/
theorem scoped_no_go (R : OrdinaryAction H n) (hn : 0 < n) :
    ¬ ForbidsEverySupportedDeltaBOne R ∧ Nonempty (OperatorWitness R) := by
  obtain ⟨W⟩ := witness_exists R hn
  exact ⟨W.not_forbids, ⟨W⟩⟩

/-- The fixed retained-spectrum class, not a general SU(5) Lagrangian. -/
structure Model (H : Type*) [CommGroup H] where
  generations : ℕ
  positive : 0 < generations
  residual : OrdinaryAction H generations

theorem Model.selection_rule_obstruction (M : Model H) :
    ¬ ForbidsEverySupportedDeltaBOne M.residual ∧ Nonempty (OperatorWitness M.residual) :=
  scoped_no_go M.residual M.positive

/-- A genuine one-generation inhabitant for any residual group, acting
trivially on the actual matter. No source certificate is supplied by hand. -/
def oneGeneration (H : Type*) [CommGroup H] : Model H where
  generations := 1
  positive := by decide
  residual := 1

theorem oneGeneration_result (H : Type*) [CommGroup H] :
    ¬ ForbidsEverySupportedDeltaBOne (oneGeneration H).residual ∧
      Nonempty (OperatorWitness (oneGeneration H).residual) :=
  (oneGeneration H).selection_rule_obstruction

end

end GUT.SU5.SelectionRule
