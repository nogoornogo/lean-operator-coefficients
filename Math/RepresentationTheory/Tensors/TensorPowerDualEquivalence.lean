import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import TauCeti.RepresentationTheory.Tensor.Power

/-! The canonical perfect mixed tensor pairing, with its actual group action. -/
namespace Math.TensorPowerDualEquivalence
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (W : Type*) [AddCommGroup W] [Module ℂ W] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n W) := inferInstance

def equivalence (n : ℕ) : Representation.Equiv
    (rho.dual.tensorPower n) (rho.tensorPower n).dual where
  toLinearEquiv := PiTensorProduct.dualDistribEquiv
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change PiTensorProduct.dualDistrib
        ((rho.dual.tensorPower n) g (PiTensorProduct.tprod ℂ f))
        (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)
        ((rho.tensorPower n) g⁻¹ (PiTensorProduct.tprod ℂ v))
    simp only [Representation.tensorPower_apply,PiTensorProduct.map_tprod,
      PiTensorProduct.dualDistrib_apply,Representation.dual_apply,Module.Dual.transpose_apply]
    rfl

def doubleDual (n : ℕ) : Representation.Equiv
    (rho.dual.tensorPower n).dual (rho.tensorPower n) :=
  (dualEquiv (equivalence rho n)).trans (bidualEquiv (rho.tensorPower n)).symm

def curry (a b : ℕ) :
    IntertwiningMap ((rho.tensorPower a).tprod (rho.dual.tensorPower b)) (trivial ℂ G ℂ) ≃ₗ[ℂ]
      IntertwiningMap (rho.tensorPower a) (rho.tensorPower b) :=
  (InvariantTensorCurry.equiv _ _).trans
    (InvariantTensorCurry.postcompose _ _ (doubleDual rho b))

theorem equivalence_tprod (n : ℕ) (f : Fin n → Module.Dual ℂ V) (v : Fin n → V) :
    equivalence rho n (PiTensorProduct.tprod ℂ f) (PiTensorProduct.tprod ℂ v) =
      ∏ i, f i (v i) := PiTensorProduct.dualDistrib_apply f v

theorem doubleDual_apply (n : ℕ) (f : Module.Dual ℂ (⨂[ℂ]^n (Module.Dual ℂ V)))
    (y : ⨂[ℂ]^n (Module.Dual ℂ V)) :
    equivalence rho n y (doubleDual rho n f) = f y := by
  have he := (Module.evalEquiv ℂ (⨂[ℂ]^n V)).apply_symm_apply
    (SplitRepresentationProjection.dualEquiv (equivalence rho n) f)
  have hv := DFunLike.congr_fun he (equivalence rho n y)
  change (equivalence rho n y) (doubleDual rho n f) =
    f ((equivalence rho n).toLinearEquiv.symm (equivalence rho n y)) at hv
  change (equivalence rho n y) (doubleDual rho n f) =
    f ((equivalence rho n).toLinearEquiv.symm ((equivalence rho n).toLinearEquiv y)) at hv
  rw [LinearEquiv.symm_apply_apply] at hv
  exact hv

theorem curry_apply (a b : ℕ)
    (f : IntertwiningMap ((rho.tensorPower a).tprod (rho.dual.tensorPower b)) (trivial ℂ G ℂ))
    (x : ⨂[ℂ]^a V) (y : ⨂[ℂ]^b (Module.Dual ℂ V)) :
    equivalence rho b y (curry rho a b f x) = f (x ⊗ₜ[ℂ] y) :=
  doubleDual_apply rho b ((InvariantTensorCurry.curry _ _ f) x) y

end
end Math.TensorPowerDualEquivalence
