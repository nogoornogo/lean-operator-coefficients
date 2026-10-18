import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Physics.StandardModel.Gauge.SMEpsilonUniqueness

open Math

/-! Every invariant ordered qque gauge coefficient is the standard epsilon tensor. -/
namespace GUT.QqueGaugeUniqueness
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor SMEpsilonUniqueness
open scoped TensorProduct

abbrev Coefficient := IntertwiningMap qqueRepresentation (Representation.trivial ℂ GaugeGroup ℂ)

def colorSlice (f : Coefficient) (x y : Weak) (e : ℂ) :
    Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ :=
  TensorProduct.curry (TensorProduct.curry (f.toLinearMap.comp
    (TensorProduct.map (TensorProduct.map ((TensorProduct.mk ℂ Color Weak).flip x)
      ((TensorProduct.mk ℂ Color Weak).flip y)) ((TensorProduct.mk ℂ Color ℂ).flip e))))

theorem colorSlice_invariant (f : Coefficient) (x y : Weak) (e : ℂ)
    (g : Matrix.specialUnitaryGroup (Fin 3) ℂ) (a b c : Color) :
    colorSlice f x y e (SmallSpecialUnitary.defining 3 g a)
      (SmallSpecialUnitary.defining 3 g b) (SmallSpecialUnitary.defining 3 g c) =
        colorSlice f x y e a b c := by
  have h := IntertwiningMap.isIntertwining _ _ f (g, 1, 1)
    (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] e))
  simpa [colorSlice, qqueRepresentation, quark, upRight, electronRight, twist,
    phase, color, weak, SmallSpecialUnitary.defining] using h

def weakSlice (f : Coefficient) (e : ℂ) : Weak →ₗ[ℂ] Weak →ₗ[ℂ] ℂ :=
  TensorProduct.curry (f.toLinearMap.comp
    (((TensorProduct.mk ℂ (Quark ⊗[ℂ] Quark) (Color ⊗[ℂ] ℂ)).flip
      (colorBasis 2 ⊗ₜ[ℂ] e)).comp
      (TensorProduct.map (TensorProduct.mk ℂ Color Weak (colorBasis 0))
        (TensorProduct.mk ℂ Color Weak (colorBasis 1)))))

theorem weakSlice_invariant (f : Coefficient) (e : ℂ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x y : Weak) :
    weakSlice f e (SmallSpecialUnitary.defining 2 g x) (SmallSpecialUnitary.defining 2 g y) =
      weakSlice f e x y := by
  have h := IntertwiningMap.isIntertwining _ _ f (1, g, 1)
    (((colorBasis 0 ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (colorBasis 1 ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (colorBasis 2 ⊗ₜ[ℂ] e))
  simpa [weakSlice, qqueRepresentation, quark, upRight, electronRight, twist,
    phase, color, weak, SmallSpecialUnitary.defining] using h

theorem eq_smul_qque (f : Coefficient) : f = f qqueWitness • qqueIntertwiner := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro x
  apply TensorProduct.ext
  apply LinearMap.ext; intro b
  apply LinearMap.ext; intro y
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro e
  have hc := congrArg (fun k => k a b c)
    (color_unique (colorSlice f x y e) (colorSlice_invariant f x y e))
  have hw := congrArg (fun k => k x y)
    (weak_unique (weakSlice f e) (weakSlice_invariant f e))
  change f (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] e)) =
    weakSlice f e x y * eps3 a b c at hc
  change weakSlice f e x y = weakSlice f e (weakBasis 0) (weakBasis 1) * eps2 x y at hw
  have he : weakSlice f e (weakBasis 0) (weakBasis 1) = e * f qqueWitness := by
    change f (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] (colorBasis 1 ⊗ₜ[ℂ] weakBasis 1)) ⊗ₜ[ℂ]
      (colorBasis 2 ⊗ₜ[ℂ] e)) = _
    conv_lhs => rw [← mul_one e]
    rw [← smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, map_smul]
    rfl
  change f (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] e)) =
    f qqueWitness * qque (((a ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] e))
  rw [hc, hw, he, qque_tmul]
  ring

end
end GUT.QqueGaugeUniqueness
