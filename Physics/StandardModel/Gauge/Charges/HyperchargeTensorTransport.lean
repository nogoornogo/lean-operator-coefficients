import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Mathlib.RepresentationTheory.Equiv
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

open Math

/-! Charge-preserving tensor regrouping. Only the sum of charges is removed
when it is zero; individual charged factors are never treated as neutral. -/
namespace Physics.HyperchargeTensorTransport
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor
open scoped TensorProduct

theorem phase_add (y z : ℤ) (g : GaugeGroup) :
    phase (y + z) g = phase y g * phase z g := by
  change (g.2.2 : ℂ) ^ (y + z) = (g.2.2 : ℂ) ^ y * (g.2.2 : ℂ) ^ z
  exact zpow_add₀ (Circle.coe_ne_zero g.2.2) y z

theorem phase_inv (y : ℤ) (g : GaugeGroup) : phase y g⁻¹ = phase (-y) g := by
  change ((g.2.2⁻¹ : Circle) : ℂ) ^ y = (g.2.2 : ℂ) ^ (-y)
  simp

noncomputable def dualLine (y : ℤ) : Representation.Equiv
    (twist (Representation.trivial ℂ GaugeGroup ℂ) y).dual
    (twist (Representation.trivial ℂ GaugeGroup ℂ) (-y)) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ
  isIntertwining' g := by
    ext f
    change f (phase y g⁻¹ • (1 : ℂ)) = phase (-y) g • f 1
    rw [map_smul, phase_inv]

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ GaugeGroup A) (b : Representation ℂ GaugeGroup B)

def tensor (y z : ℤ) : Representation.Equiv
    ((twist a y).tprod (twist b z)) (twist (a.tprod b) (y + z)) where
  toLinearEquiv := LinearEquiv.refl ℂ (A ⊗[ℂ] B)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro w
    change (phase y g • a g x) ⊗ₜ[ℂ] (phase z g • b g w) =
      phase (y + z) g • (a g x ⊗ₜ[ℂ] b g w)
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_smul, phase_add, mul_comm]

def neutral : Representation.Equiv (twist a 0) a where
  toLinearEquiv := LinearEquiv.refl ℂ A
  isIntertwining' g := by
    ext x
    simp [twist, phase]

def neutralOfEq (y : ℤ) (hy : y = 0) : Representation.Equiv (twist a y) a := by
  subst y
  exact neutral a

variable {C D E : Type*} [AddCommGroup C] [Module ℂ C]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
  (c : Representation ℂ GaugeGroup C) (d : Representation ℂ GaugeGroup D)
  (e : Representation ℂ GaugeGroup E)

def four (y₀ y₁ y₂ y₃ : ℤ) : Representation.Equiv
    (((twist a y₀).tprod (twist b y₁)).tprod ((twist c y₂).tprod (twist d y₃)))
    (twist ((a.tprod b).tprod (c.tprod d)) ((y₀ + y₁) + (y₂ + y₃))) :=
  (ExternalInvariantTensor.tensorEquiv (tensor a b y₀ y₁) (tensor c d y₂ y₃)).trans
    (tensor (a.tprod b) (c.tprod d) (y₀ + y₁) (y₂ + y₃))

def five (y₀ y₁ y₂ y₃ y₄ : ℤ) : Representation.Equiv
    ((((twist a y₀).tprod (twist b y₁)).tprod ((twist c y₂).tprod (twist d y₃))).tprod
      (twist e y₄))
    (twist (V := ((A ⊗[ℂ] B) ⊗[ℂ] (C ⊗[ℂ] D)) ⊗[ℂ] E)
      (((a.tprod b).tprod (c.tprod d)).tprod e)
      (((y₀ + y₁) + (y₂ + y₃)) + y₄)) :=
  (ExternalInvariantTensor.tensorEquiv (four a b c d y₀ y₁ y₂ y₃)
    (Representation.Equiv.refl (twist e y₄))).trans
    (tensor ((a.tprod b).tprod (c.tprod d)) e ((y₀ + y₁) + (y₂ + y₃)) y₄)

def fiveNeutral (y₀ y₁ y₂ y₃ y₄ : ℤ)
    (hy : ((y₀ + y₁) + (y₂ + y₃)) + y₄ = 0) : Representation.Equiv
    ((((twist a y₀).tprod (twist b y₁)).tprod ((twist c y₂).tprod (twist d y₃))).tprod
      (twist e y₄)) (((a.tprod b).tprod (c.tprod d)).tprod e) :=
  (five a b c d e y₀ y₁ y₂ y₃ y₄).trans
    (neutralOfEq (A := ((A ⊗[ℂ] B) ⊗[ℂ] (C ⊗[ℂ] D)) ⊗[ℂ] E)
      (((a.tprod b).tprod (c.tprod d)).tprod e) _ hy)

end
end Physics.HyperchargeTensorTransport
