import TauCeti.RepresentationTheory.Tensor.Power
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Tensoring an actual representation equivalence in every slot. -/
namespace Math.TensorPowerEquivalence
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G V} {sigma : Representation ℂ G W}

def equivalence (e : Representation.Equiv rho sigma) (n : ℕ) :
    Representation.Equiv (rho.tensorPower n) (sigma.tensorPower n) where
  toLinearEquiv := PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv)
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change (PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv))
        ((rho.tensorPower n) g (PiTensorProduct.tprod ℂ v)) =
      (sigma.tensorPower n) g
        (PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv) (PiTensorProduct.tprod ℂ v))
    simp only [Representation.tensorPower_apply,PiTensorProduct.map_tprod,
      PiTensorProduct.congr_tprod]
    congr 1
    funext i
    exact e.isIntertwining _ _ g (v i)

theorem tprod (e : Representation.Equiv rho sigma) (n : ℕ) (v : Fin n → V) :
    equivalence e n (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => e (v i)) := PiTensorProduct.congr_tprod _ _

theorem symm_tprod (e : Representation.Equiv rho sigma) (n : ℕ) (v : Fin n → W) :
    (equivalence e n).symm (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => e.symm (v i)) := PiTensorProduct.congr_symm_tprod _ _

def one (rho : Representation ℂ G V) : Representation.Equiv (rho.tensorPower 1) rho where
  toLinearEquiv := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp [Representation.tensorPower_apply,PiTensorProduct.map_tprod]

end
end Math.TensorPowerEquivalence
