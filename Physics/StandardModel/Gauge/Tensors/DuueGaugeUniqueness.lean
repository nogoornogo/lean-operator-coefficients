import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness
import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor

open Math

/-! The duue gauge line, ordered as u,u,d,e for repeated-species descent. -/
namespace Physics.DuueGaugeUniqueness
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor SMEpsilonTensor SMEpsilonUniqueness
open scoped TensorProduct

def representation := (upRight.tprod upRight).tprod (downRight.tprod electronRight)
abbrev Coefficient := IntertwiningMap representation (Representation.trivial ℂ GaugeGroup ℂ)

def contraction : ((Color ⊗[ℂ] Color) ⊗[ℂ] (Color ⊗[ℂ] ℂ)) →ₗ[ℂ] ℂ :=
  ((TensorProduct.rid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map colorTensor LinearMap.id)).comp
      (TensorProduct.assoc ℂ (Color ⊗[ℂ] Color) Color ℂ).symm.toLinearMap

@[simp] theorem contraction_apply (a b c : Color) (z : ℂ) :
    contraction ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] z)) = eps3 a b c * z := by
  simp [contraction, mul_comm]

theorem phases (g : GaugeGroup) : phase 4 g * phase 4 g * phase (-2) g * phase (-6) g = 1 := by
  have h : g.2.2 ^ (4 : ℤ) * g.2.2 ^ (4 : ℤ) * g.2.2 ^ (-2 : ℤ) *
      g.2.2 ^ (-6 : ℤ) = 1 := by group
  change (↑(g.2.2 ^ (4 : ℤ)) : ℂ) * ↑(g.2.2 ^ (4 : ℤ)) *
    ↑(g.2.2 ^ (-2 : ℤ)) * ↑(g.2.2 ^ (-6 : ℤ)) = 1
  simpa only [Circle.coe_mul, Circle.coe_one] using congrArg ((↑) : Circle → ℂ) h

def intertwiner : Coefficient where
  toLinearMap := contraction
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    apply TensorProduct.ext
    apply LinearMap.ext; intro c
    apply LinearMap.ext; intro z
    simp [representation, upRight, downRight, electronRight, twist,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, color, Matrix.toLin'_apply,
      eps3_invariant _ g.1.prop.2]
    linear_combination (eps3 a b c * z) * phases g

def witness := (colorBasis 0 ⊗ₜ[ℂ] colorBasis 1) ⊗ₜ[ℂ] (colorBasis 2 ⊗ₜ[ℂ] (1 : ℂ))

theorem normalized : intertwiner witness = 1 := by simp [intertwiner, witness]

def slice (f : Coefficient) : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ :=
  TensorProduct.curry (TensorProduct.curry (f.toLinearMap.comp
    (TensorProduct.map LinearMap.id ((TensorProduct.mk ℂ Color ℂ).flip 1))))

theorem slice_invariant (f : Coefficient) (g : Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (a b c : Color) :
    slice f (SmallSpecialUnitary.defining 3 g a) (SmallSpecialUnitary.defining 3 g b)
      (SmallSpecialUnitary.defining 3 g c) = slice f a b c := by
  have h := IntertwiningMap.isIntertwining _ _ f (g,1,1)
    ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] (1 : ℂ)))
  simpa [slice, representation, upRight, downRight, electronRight, twist,
    phase, color, SmallSpecialUnitary.defining] using h

theorem unique (f : Coefficient) : f = f witness • intertwiner := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro a
  apply LinearMap.ext; intro b
  apply TensorProduct.ext
  apply LinearMap.ext; intro c
  apply LinearMap.ext; intro z
  have h := congrArg (fun k => k a b c) (color_unique (slice f) (slice_invariant f))
  change f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] (1 : ℂ))) = f witness * eps3 a b c at h
  have hz : c ⊗ₜ[ℂ] z = z • (c ⊗ₜ[ℂ] (1 : ℂ)) := by
    rw [← TensorProduct.tmul_smul]
    simp
  change f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] z)) =
    f witness * contraction ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] z))
  rw [contraction_apply]
  rw [hz, TensorProduct.tmul_smul, map_smul, smul_eq_mul, h]
  ring

end
end Physics.DuueGaugeUniqueness
