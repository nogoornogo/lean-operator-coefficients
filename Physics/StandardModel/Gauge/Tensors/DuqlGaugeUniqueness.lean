import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness

open Math

/-! The entire ordered duql gauge-invariant space is the normalized epsilon line. -/
namespace Physics.DuqlGaugeUniqueness
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor SMEpsilonUniqueness
open scoped TensorProduct

abbrev Coefficient := IntertwiningMap duqlRepresentation (Representation.trivial ℂ GaugeGroup ℂ)

def colorSlice (f : Coefficient) (x y : Weak) :
    Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ :=
  TensorProduct.curry (TensorProduct.curry (f.toLinearMap.comp
    (TensorProduct.map (LinearMap.id) (((TensorProduct.mk ℂ Quark Weak).flip y).comp
      ((TensorProduct.mk ℂ Color Weak).flip x)))))

theorem colorSlice_invariant (f : Coefficient) (x y : Weak)
    (g : Matrix.specialUnitaryGroup (Fin 3) ℂ) (a b c : Color) :
    colorSlice f x y (SmallSpecialUnitary.defining 3 g a)
      (SmallSpecialUnitary.defining 3 g b) (SmallSpecialUnitary.defining 3 g c) =
        colorSlice f x y a b c := by
  have h := IntertwiningMap.isIntertwining _ _ f (g, 1, 1)
    ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y))
  simpa [colorSlice, duqlRepresentation, downRight, upRight, quark, lepton, twist,
    phase, color, weak, SmallSpecialUnitary.defining] using h

def weakSlice (f : Coefficient) : Weak →ₗ[ℂ] Weak →ₗ[ℂ] ℂ :=
  TensorProduct.curry (f.toLinearMap.comp
    ((TensorProduct.mk ℂ (Color ⊗[ℂ] Color) (Quark ⊗[ℂ] Weak)
      (colorBasis 0 ⊗ₜ[ℂ] colorBasis 1)).comp
      (TensorProduct.map (TensorProduct.mk ℂ Color Weak (colorBasis 2)) LinearMap.id)))

theorem weakSlice_invariant (f : Coefficient)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x y : Weak) :
    weakSlice f (SmallSpecialUnitary.defining 2 g x) (SmallSpecialUnitary.defining 2 g y) =
      weakSlice f x y := by
  have h := IntertwiningMap.isIntertwining _ _ f (1, g, 1)
    ((colorBasis 0 ⊗ₜ[ℂ] colorBasis 1) ⊗ₜ[ℂ] ((colorBasis 2 ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y))
  simpa [weakSlice, duqlRepresentation, downRight, upRight, quark, lepton, twist,
    phase, color, weak, SmallSpecialUnitary.defining] using h

theorem unique (f : Coefficient) : f = f duqlWitness • duqlIntertwiner := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro b
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  have hc := congrArg (fun k => k a b c)
    (color_unique (colorSlice f x y) (colorSlice_invariant f x y))
  have hw := congrArg (fun k => k x y)
    (weak_unique (weakSlice f) (weakSlice_invariant f))
  change f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y)) =
    weakSlice f x y * eps3 a b c at hc
  change weakSlice f x y = f duqlWitness * eps2 x y at hw
  change f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y)) =
    f duqlWitness * duql ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y))
  rw [hc, hw, duql_tmul]
  ring

end
end Physics.DuqlGaugeUniqueness
