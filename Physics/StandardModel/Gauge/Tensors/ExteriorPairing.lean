import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor

/-! Charged color/weak alternating contractions used by actual exterior
branching. These identities involve only the SM covering group. -/

set_option autoImplicit false

namespace Physics.StandardSMExterior

noncomputable section

open StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

private theorem color_phases (g : GaugeGroup) :
    phase (-2) g * phase (-2) g * phase 4 g = 1 := by
  change (↑(g.2.2 ^ (-2 : ℤ)) : ℂ) * ↑(g.2.2 ^ (-2 : ℤ)) * ↑(g.2.2 ^ (4 : ℤ)) = 1
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have h : g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (-2 : ℤ) * g.2.2 ^ (4 : ℤ) = 1 := by group
  rw [h, Circle.coe_one]

theorem color_pair_invariant (g : GaugeGroup) (a b c : Color) :
    eps3 (twist color (-2) g a) (twist color (-2) g b) (upRight g c) = eps3 a b c := by
  simp [twist, color, upRight, Matrix.toLin'_apply, eps3_invariant _ g.1.prop.2]
  linear_combination eps3 a b c * color_phases g

private theorem weak_phases (g : GaugeGroup) : phase 3 g * phase 3 g * phase (-6) g = 1 := by
  change (↑(g.2.2 ^ (3 : ℤ)) : ℂ) * ↑(g.2.2 ^ (3 : ℤ)) * ↑(g.2.2 ^ (-6 : ℤ)) = 1
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have h : g.2.2 ^ (3 : ℤ) * g.2.2 ^ (3 : ℤ) * g.2.2 ^ (-6 : ℤ) = 1 := by group
  rw [h, Circle.coe_one]

theorem weak_pair_invariant (g : GaugeGroup) (a b : Weak) (z : ℂ) :
    eps2 (twist weak 3 g a) (twist weak 3 g b) * electronRight g z = eps2 a b * z := by
  simp [twist, weak, electronRight, Matrix.toLin'_apply, eps2_invariant _ g.2.1.prop.2]
  linear_combination (eps2 a b * z) * weak_phases g

theorem mixed_pair_covariant (g : GaugeGroup) (a : Color) (b : Weak) :
    twist color (-2) g a ⊗ₜ[ℂ] twist weak 3 g b = quark g (a ⊗ₜ[ℂ] b) := by
  have hp : phase (-2) g * phase 3 g = phase 1 g := by
    change (↑(g.2.2 ^ (-2 : ℤ)) : ℂ) * ↑(g.2.2 ^ (3 : ℤ)) = ↑(g.2.2 ^ (1 : ℤ))
    rw [← Circle.coe_mul, ← zpow_add]
    rfl
  simp [quark, twist, Representation.tprod_apply, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_smul, mul_comm (phase 3 g) (phase (-2) g), hp]

end

end Physics.StandardSMExterior
