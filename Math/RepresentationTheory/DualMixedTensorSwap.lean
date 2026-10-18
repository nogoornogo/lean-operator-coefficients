import Math.RepresentationTheory.TensorPowerEquivalence
import Math.RepresentationTheory.ExternalInvariantTensor
import Mathlib.RingTheory.TensorProduct.Finite

/-! Actual mixed tensors for a dual representation normalize by biduality
and exchange their vector/covector degrees. -/
namespace Math.DualMixedTensorSwap
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

def equivalence (p q : ℕ) : Representation.Equiv
    ((rho.dual.tensorPower p).tprod (rho.dual.dual.tensorPower q))
      ((rho.tensorPower q).tprod (rho.dual.tensorPower p)) :=
  (Representation.TensorProduct.comm _ _).trans
    (tensorEquiv (TensorPowerEquivalence.equivalence (bidualEquiv rho).symm q)
      (.refl (rho.dual.tensorPower p)))

theorem symm_tprod (p q : ℕ) (v : Fin q → V) (f : Fin p → Module.Dual ℂ V) :
    (equivalence rho p q).symm (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => Module.Dual.eval ℂ V (v i)) := by
  change TensorProduct.comm ℂ _ _
    (TensorProduct.congr
      (TensorPowerEquivalence.equivalence (bidualEquiv rho).symm q).toLinearEquiv.symm
      (.refl ℂ _)
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f)) = _
  rw [TensorProduct.congr_tmul]
  change TensorProduct.comm ℂ _ _
    ((TensorPowerEquivalence.equivalence (bidualEquiv rho).symm q).symm
      (PiTensorProduct.tprod ℂ v) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) = _
  rw [TensorPowerEquivalence.symm_tprod]
  rfl

theorem tprod (p q : ℕ) (v : Fin q → V) (f : Fin p → Module.Dual ℂ V) :
    equivalence rho p q
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => Module.Dual.eval ℂ V (v i))) =
      PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f := by
  rw [← symm_tprod rho p q v f,Representation.Equiv.apply_symm_apply]

end
end Math.DualMixedTensorSwap
