import Math.RepresentationTheory.TraceFreeCoefficientExclusion
import Math.RepresentationTheory.TraceFreeTrilinear
import Math.RepresentationTheory.SU3TensorPositive
import Math.RepresentationTheory.SU3CompatibleCoupling

/-! Exact support of every tensor power of the actual trace-free color
branch, via pair/triple witnesses and the Schur singleton exclusion.
No numerical multiplicity or color irreducibility premise is used. -/
namespace Math.SU3TraceFreePowers
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior TraceEndomorphismSplit
open InvariantCoefficientProduct ExternalInvariantTensor
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (r : Representation ℂ Group V)
@[reducible] local instance : AddCommGroup (TraceFree r) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (TraceFree r ⊗[ℂ] TraceFree r) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup ((TraceFree r ⊗[ℂ] TraceFree r) ⊗[ℂ] TraceFree r) := Module.addCommMonoidToAddCommGroup ℂ
abbrev free := traceFreeAction r
def HasScalar (n : ℕ) : Prop := HasUnit ((free r).tensorPower n)

def twoEquiv : Representation.Equiv ((free r).tensorPower 2) ((free r).tprod (free r)) :=
  ((free r).tensorPowerAddEquiv 1 1).symm.trans
    (tensorEquiv (SU3TensorPositive.oneEquiv (free r)) (SU3TensorPositive.oneEquiv (free r)))

def threeEquiv : Representation.Equiv ((free r).tensorPower 3) (TraceFreeTrilinear.action r) :=
  ((free r).tensorPowerAddEquiv 2 1).symm.trans
    (tensorEquiv (twoEquiv r) (SU3TensorPositive.oneEquiv (free r)))

omit [FiniteDimensional ℂ V] in
theorem zero : HasScalar r 0 :=
  transport (SU3TensorPositive.zeroEquiv (free r)).symm ⟨IntertwiningMap.id _,1,rfl⟩

omit [FiniteDimensional ℂ V] in
theorem add {m n : ℕ} (hm : HasScalar r m) (hn : HasScalar r n) : HasScalar r (m+n) :=
  transport ((free r).tensorPowerAddEquiv m n) (tensor hm hn)

variable (b : Module.Basis (Fin 3) ℂ V)

include b in
theorem pair : HasScalar r 2 :=
  transport (twoEquiv r).symm (TraceFreePairing.unit r b 0 1 (by decide))

include b in
theorem triple : HasScalar r 3 :=
  transport (threeEquiv r).symm (TraceFreeTrilinear.unit r b)

include b in
theorem positive (n : ℕ) (hn : n≠1) : HasScalar r n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n=0
    · subst n; exact zero r
    by_cases h2 : n=2
    · subst n; exact pair r b
    by_cases h3 : n=3
    · subst n; exact triple r b
    have h4 : 4≤n := by omega
    have hh := add r (ih (n-2) (by omega) (by omega)) (pair r b)
    have he : n-2+2=n := by omega
    simpa only [he] using hh

include b in
theorem allowed_iff [IsIrreducible r] (n : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants ((free r).tensorPower n)) ↔ n≠1 := by
  constructor
  · intro h hn
    subst n
    have hf := (SelectionCriteria.allowed_equiv
      (InvariantCoefficientTransport.alongEquiv (SU3TensorPositive.oneEquiv (free r)))).mp h
    have hd : Module.finrank ℂ V≠0 := by
      rw [Module.finrank_eq_card_basis b,Fintype.card_fin]
      exact Nat.succ_ne_zero 2
    exact ((SelectionCriteria.forbidden_iff_not_allowed _).mp
      (TraceFreeCoefficientExclusion.forbidden r hd)) hf
  · intro h
    exact (hasUnit_iff _).mp (positive r b n h)

theorem defining_iff (n : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants ((free rho).tensorPower n)) ↔ n≠1 :=
  allowed_iff rho basis n

theorem dual_defining_iff (n : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants ((free rho.dual).tensorPower n)) ↔ n≠1 :=
  allowed_iff rho.dual SU3DualExterior.basis n

include b in
theorem joint_iff [IsIrreducible r] (n a c d e : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants
      (external ((free r).tensorPower n) (SU3CompatibleCoupling.spinPair a c d e))) ↔
      n≠1 ∧ a=d ∧ c=e := by
  rw [ExternalCoefficientSupport.allowed_iff,allowed_iff r b,
    SU3CompatibleCoupling.spin_iff]

end
end Math.SU3TraceFreePowers
