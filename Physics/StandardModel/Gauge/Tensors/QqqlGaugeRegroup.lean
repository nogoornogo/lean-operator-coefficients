import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

/-! Physical qqql gauge fields regroup into color and weak tensors.
Hypercharge cancels as 1 + 1 + 1 - 3 = 0, proved on the group action. -/
namespace Physics.QqqlGaugeRegroup
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

def representation := (quark.tprod quark).tprod (quark.tprod lepton)
def regrouped := ((color.tprod color).tprod color).tprod
  ((weak.tprod weak).tprod (weak.tprod weak))

def linearEquiv : ((Quark ⊗[ℂ] Quark) ⊗[ℂ] (Quark ⊗[ℂ] Weak)) ≃ₗ[ℂ]
    (((Color ⊗[ℂ] Color) ⊗[ℂ] Color) ⊗[ℂ]
      ((Weak ⊗[ℂ] Weak) ⊗[ℂ] (Weak ⊗[ℂ] Weak))) :=
  (TensorProduct.congr (TensorProduct.tensorTensorTensorComm ℂ Color Weak Color Weak)
    (TensorProduct.assoc ℂ Color Weak Weak)).trans
      (TensorProduct.tensorTensorTensorComm ℂ (Color ⊗[ℂ] Color) (Weak ⊗[ℂ] Weak) Color (Weak ⊗[ℂ] Weak))

theorem linearEquiv_apply (a b c : Color) (x y z w : Weak) :
    linearEquiv (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] w)) =
      ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) := rfl

theorem phases (g : GaugeGroup) : phase 1 g * phase 1 g * phase 1 g * phase (-3) g = 1 := by
  have h : g.2.2 ^ (1 : ℤ) * g.2.2 ^ (1 : ℤ) * g.2.2 ^ (1 : ℤ) * g.2.2 ^ (-3 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (1 : ℤ)) : ℂ) * ↑(g.2.2 ^ (1 : ℤ)) *
    ↑(g.2.2 ^ (1 : ℤ)) * ↑(g.2.2 ^ (-3 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

def equiv : Representation.Equiv representation regrouped where
  toLinearEquiv := linearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro x
    apply TensorProduct.ext
    apply LinearMap.ext; intro b
    apply LinearMap.ext; intro y
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro c
    apply LinearMap.ext; intro z
    apply LinearMap.ext; intro w
    change linearEquiv (representation g (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] w))) = regrouped g (linearEquiv
        (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] w)))
    change linearEquiv
      (((phase 1 g • ((color g a) ⊗ₜ[ℂ] (weak g x))) ⊗ₜ[ℂ]
        (phase 1 g • ((color g b) ⊗ₜ[ℂ] (weak g y)))) ⊗ₜ[ℂ]
        ((phase 1 g • ((color g c) ⊗ₜ[ℂ] (weak g z))) ⊗ₜ[ℂ]
          (phase (-3) g • weak g w))) =
      ((color g a ⊗ₜ[ℂ] color g b) ⊗ₜ[ℂ] color g c) ⊗ₜ[ℂ]
        ((weak g x ⊗ₜ[ℂ] weak g y) ⊗ₜ[ℂ] (weak g z ⊗ₜ[ℂ] weak g w))
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
      linearEquiv_apply]
    simp only [smul_smul]
    have hp : phase (-3) g * (phase 1 g * (phase 1 g * phase 1 g)) = 1 := by
      convert phases g using 1; ring
    rw [hp, one_smul]

end
end Physics.QqqlGaugeRegroup
