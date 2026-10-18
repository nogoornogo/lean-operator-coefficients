import Math.RepresentationTheory.TraceFreePairing
import Math.RepresentationTheory.SU3ColorPair
import Math.RepresentationTheory.SU3DualExterior
import Math.RepresentationTheory.SymmetricDualPairing

/-! Positive couplings for actual reachable colored branches, with explicit
witnesses and no irreducibility assumption. These do not exhaust arbitrary
products of restricted Schur summands. -/
namespace Math.SU3ColorPositive
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior InvariantCoefficientProduct
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

abbrev symmetricCarrier (m : ℕ) := Sym[ℂ]^m Vector ⊗[ℂ] Sym[ℂ]^m (Module.Dual ℂ Vector)
@[reducible] local instance (m : ℕ) : AddCommGroup (symmetricCarrier m) := inferInstance
abbrev symmetricPair (m : ℕ) : Representation ℂ Group (symmetricCarrier m) :=
  (rho.symmetricPower m).tprod (rho.dual.symmetricPower m)

theorem symmetric_unit (m : ℕ) : HasUnit (symmetricPair m) :=
  ⟨SymmetricDualPairing.coefficient rho m,
    SymmetricPower.tprod ℂ (fun _ : Fin m => basis 0) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin m => basis.coord 0),by
        rw [SymmetricDualPairing.coefficient_diagonal]
        simp⟩

theorem symmetric_allowed (m : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (symmetricPair m)) :=
  (hasUnit_iff (symmetricPair m)).mp (symmetric_unit m)

abbrev adjointPair := TraceFreePairing.pairAction rho
abbrev dualAdjointPair := TraceFreePairing.pairAction rho.dual

theorem adjoint_unit : HasUnit adjointPair :=
  TraceFreePairing.unit rho basis (0 : Fin 3) 1 (by decide)

theorem dual_adjoint_unit : HasUnit dualAdjointPair :=
  TraceFreePairing.unit rho.dual SU3DualExterior.basis (0 : Fin 3) 1 (by decide)

theorem adjoint_allowed : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants adjointPair) :=
  (hasUnit_iff adjointPair).mp adjoint_unit

theorem dual_adjoint_allowed : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants dualAdjointPair) :=
  (hasUnit_iff dualAdjointPair).mp dual_adjoint_unit

end
end Math.SU3ColorPositive
