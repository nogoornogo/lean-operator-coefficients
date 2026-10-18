import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

/-! Left Grassmann differentiation is mathlib's Clifford contraction at
zero quadratic form, not a separately postulated derivative. -/
namespace Math.ExteriorLeftDerivative
set_option autoImplicit false
noncomputable section
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
abbrev A := ExteriorAlgebra k V

def derivative (d : Module.Dual k V) : A (k := k) (V := V) →ₗ[k] A (k := k) (V := V) :=
  CliffordAlgebra.contractLeft d

theorem generator_mul (d : Module.Dual k V) (v : V) (x : A (k := k) (V := V)) :
    derivative d (ExteriorAlgebra.ι k v*x) =
      d v • x - ExteriorAlgebra.ι k v * derivative d x :=
  CliffordAlgebra.contractLeft_ι_mul d v x

theorem leibniz (d : Module.Dual k V) (x y : A (k := k) (V := V)) :
    derivative d (x*y) = derivative d x*y + CliffordAlgebra.involute x*derivative d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [derivative, CliffordAlgebra.contractLeft_algebraMap_mul]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
  | ι_mul v x hx =>
    simp only [mul_assoc, generator_mul, hx, map_mul, CliffordAlgebra.involute_ι]
    simp only [smul_mul_assoc, mul_add, sub_mul, neg_mul, mul_assoc]
    abel

end
end Math.ExteriorLeftDerivative
