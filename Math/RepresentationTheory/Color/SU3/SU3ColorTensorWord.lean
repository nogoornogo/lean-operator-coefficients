import Math.RepresentationTheory.Color.SU3.SU3TensorTriality

/-! Closed positive coupling for arbitrary binary words of defining and
contragredient SU3 color, with the actual field order retained. -/
namespace Math.SU3ColorTensorWord
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior ExternalInvariantTensor InvariantCoefficientProduct
open scoped TensorProduct

inductive Word
  | empty
  | defining
  | dual
  | tensor (left right : Word)

open Word

structure Data where
  Carrier : Type
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  action : Representation ℂ Group Carrier
attribute [instance] Data.additive Data.linear

def data : Word → Data
  | .empty => { Carrier := ℂ,action := trivial ℂ Group ℂ }
  | .defining => { Carrier := Vector,action := rho }
  | .dual => { Carrier := Module.Dual ℂ Vector,action := rho.dual }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Word) := (data w).Carrier
abbrev action (w : Word) := (data w).action

def positiveCount : Word → ℕ
  | .empty => 0
  | .defining => 1
  | .dual => 0
  | .tensor l r => positiveCount l+positiveCount r

def negativeCount : Word → ℕ
  | .empty => 0
  | .defining => 0
  | .dual => 1
  | .tensor l r => negativeCount l+negativeCount r

@[reducible] local instance (a b : ℕ) : AddCommGroup (SU3TensorPositive.MixedCarrier a b) := inferInstance

def emptyEquiv : Representation.Equiv (action .empty) (SU3TensorPositive.mixed 0 0) :=
  ((tensorEquiv (SU3TensorPositive.zeroEquiv rho) (SU3TensorPositive.zeroEquiv rho.dual)).trans
    (Representation.TensorProduct.lid ℂ (trivial ℂ Group ℂ))).symm

def definingEquiv : Representation.Equiv (action .defining) (SU3TensorPositive.mixed 1 0) :=
  ((tensorEquiv (SU3TensorPositive.oneEquiv rho) (SU3TensorPositive.zeroEquiv rho.dual)).trans
    (Representation.TensorProduct.rid ℂ rho)).symm

def dualEquiv : Representation.Equiv (action .dual) (SU3TensorPositive.mixed 0 1) :=
  ((tensorEquiv (SU3TensorPositive.zeroEquiv rho) (SU3TensorPositive.oneEquiv rho.dual)).trans
    (Representation.TensorProduct.lid ℂ rho.dual)).symm

/-- A semantic reordering equivalence, with counts added at tensor nodes. -/
def equivalence : (w : Word) → Representation.Equiv (action w)
    (SU3TensorPositive.mixed (positiveCount w) (negativeCount w))
  | .empty => emptyEquiv
  | .defining => definingEquiv
  | .dual => dualEquiv
  | .tensor l r => (tensorEquiv (equivalence l) (equivalence r)).trans
      (SU3TensorPositive.regroup (positiveCount l) (negativeCount l) (positiveCount r) (negativeCount r))

/-- Actual invariant permission for every ordered binary color word. -/
theorem allowed_iff (w : Word) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action w)) ↔
      positiveCount w%3=negativeCount w%3 :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv (equivalence w))).trans
    (SU3TensorTriality.allowed_iff _ _)

theorem forbidden_iff (w : Word) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (action w)) ↔
      positiveCount w%3≠negativeCount w%3 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]

end
end Math.SU3ColorTensorWord
