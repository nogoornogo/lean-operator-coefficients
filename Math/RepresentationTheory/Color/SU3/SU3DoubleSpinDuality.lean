import Math.RepresentationTheory.Exterior.ExteriorDualEquivalence
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinExterior

/-! Actual dual-color Q cores are the full algebraic duals of positive
cores after the proved weak/spin doublet self-dualities. This transports
every exterior degree without recomputing its decomposition. -/
namespace Math.SU3DoubleSpinDuality
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

def spinSelfDual : Representation.Equiv spin spin.dual where
  toLinearEquiv := SU2DoubletDuality.equivalence.toLinearEquiv
  isIntertwining' g := SU2DoubletDuality.equivalence.isIntertwining' (spinProjection g)

def fieldEquivalence : Representation.Equiv dualTensor tensor.dual :=
  (tensorEquiv (tensorEquiv (.refl color.dual) SU3DoubleSpinExterior.weakSelfDual) spinSelfDual).trans
    ((tensorEquiv (InvariantTensorCurry.tensorDual color weak) (.refl spin.dual)).trans
      (InvariantTensorCurry.tensorDual (color.tprod weak) spin))

def exterior (n : ℕ) : Representation.Equiv (dualTensor.exteriorPower n) (tensor.exteriorPower n).dual :=
  (fieldEquivalence.exteriorPower n).trans (ExteriorDualEquivalence.equivalence tensor n)

end
end Math.SU3DoubleSpinDuality
