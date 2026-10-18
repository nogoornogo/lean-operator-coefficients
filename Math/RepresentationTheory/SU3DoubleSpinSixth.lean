import Math.RepresentationTheory.ColorWeakSixthAssembly
import Math.RepresentationTheory.SU3DoubleSpinFifth

/-! The complete middle Q exterior decomposition in the established
color/weak/spin group order. -/
namespace Math.SU3DoubleSpinSixth
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

abbrev positiveBranches := SU3DoubleSpinFifth.pull ColorWeakSixthAssembly.branches

def positive : Representation.Equiv (tensor.exteriorPower 6) positiveBranches :=
  (SU3DoubleSpinFifth.sourceEquiv.exteriorPower 6).trans
    (restrictEquiv ColorWeakSixthAssembly.equivalence SU3DoubleSpinFifth.reorder)

def negative : Representation.Equiv (dualTensor.exteriorPower 6) positiveBranches.dual :=
  (SU3DoubleSpinDuality.exterior 6).trans (dualEquiv positive)

end
end Math.SU3DoubleSpinSixth
