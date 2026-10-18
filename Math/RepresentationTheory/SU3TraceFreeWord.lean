import Math.RepresentationTheory.SU3TraceFreePowers
import Math.RepresentationTheory.TraceFreeDualEnd
import Math.RepresentationTheory.SU3ColorTensorWord

/-! Complete support for arbitrary ordered tensor words of the actual
defining/dual trace-free color branches. Both orientations are compared
by a proved equivalence before the tensor-power criterion is applied. -/
namespace Math.SU3TraceFreeWord
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior ExternalInvariantTensor
abbrev Data := SU3ColorTensorWord.Data
@[reducible] local instance : AddCommGroup (TraceEndomorphismSplit.TraceFree rho) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (TraceEndomorphismSplit.TraceFree rho.dual) :=
  Module.addCommMonoidToAddCommGroup ℂ
open scoped TensorProduct

inductive Word
  | empty
  | direct
  | conjugate
  | tensor (left right : Word)

@[reducible] def data : Word → Data
  | .empty => { Carrier := ℂ,action := trivial ℂ Group ℂ }
  | .direct =>
    { Carrier := TraceEndomorphismSplit.TraceFree rho,action := SU3TraceFreePowers.free rho }
  | .conjugate =>
    { Carrier := TraceEndomorphismSplit.TraceFree rho.dual,action := SU3TraceFreePowers.free rho.dual }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Word) := (data w).Carrier
abbrev action (w : Word) := (data w).action

def count : Word → ℕ
  | .empty => 0
  | .direct => 1
  | .conjugate => 1
  | .tensor l r => count l+count r

def orientations : Representation.Equiv (SU3TraceFreePowers.free rho.dual) (SU3TraceFreePowers.free rho) :=
  (TraceFreeDualEnd.equivalence rho SU3ColorPair.dimension_nonzero).symm

def equivalence : (w : Word) → Representation.Equiv (action w)
    ((SU3TraceFreePowers.free rho).tensorPower (count w))
  | .empty => (SU3TensorPositive.zeroEquiv (SU3TraceFreePowers.free rho)).symm
  | .direct => (SU3TensorPositive.oneEquiv (SU3TraceFreePowers.free rho)).symm
  | .conjugate => orientations.trans (SU3TensorPositive.oneEquiv (SU3TraceFreePowers.free rho)).symm
  | .tensor l r => (tensorEquiv (equivalence l) (equivalence r)).trans
      ((SU3TraceFreePowers.free rho).tensorPowerAddEquiv (count l) (count r))

theorem allowed_iff (w : Word) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants (action w)) ↔ count w≠1 :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv (equivalence w))).trans
    (SU3TraceFreePowers.defining_iff (count w))

theorem forbidden_iff (w : Word) : SelectionCriteria.Forbidden
    (InvariantCoefficientTransport.Invariants (action w)) ↔ count w=1 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff,not_not]

theorem joint_iff (w : Word) (a b c d : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants
      (external (action w) (SU3CompatibleCoupling.spinPair a b c d))) ↔
      count w≠1 ∧ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,allowed_iff,SU3CompatibleCoupling.spin_iff]

end
end Math.SU3TraceFreeWord
