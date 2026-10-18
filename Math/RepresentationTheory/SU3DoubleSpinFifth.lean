import Math.RepresentationTheory.ColorWeakFifthAssembly
import Math.RepresentationTheory.SU3DoubleSpinExterior
import Math.RepresentationTheory.SU3DoubleSpinDuality

/-! Transport the complete fifth-degree decomposition to the established
color/weak/spin group order, retaining the actual Q-core source. -/
namespace Math.SU3DoubleSpinFifth
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Doublet ⊗[ℂ] (Color ⊗[ℂ] Doublet)) := inferInstance

def reorder : Group →* WeakDoubletScalars.Group × ColorWeakMiddleGauge.Group where
  toFun g := (g.2.2,(g.1,g.2.1))
  map_one' := rfl
  map_mul' _ _ := rfl

def pull {A : Type*} [AddCommMonoid A] [Module ℂ A]
    (r : Representation ℂ (WeakDoubletScalars.Group × ColorWeakMiddleGauge.Group) A) :
    Representation ℂ Group A := r.comp reorder

abbrev positiveBranches := pull ColorWeakFifthAssembly.branches

def sourceEquiv : Representation.Equiv tensor
    (pull (external WeakDoubletScalars.doublet ColorWeakMiddleGauge.gauge)) where
  toLinearEquiv := TensorProduct.comm ℂ (Color ⊗[ℂ] Doublet) Doublet
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    rfl

def positive : Representation.Equiv (tensor.exteriorPower 5) positiveBranches :=
  (sourceEquiv.exteriorPower 5).trans (restrictEquiv ColorWeakFifthAssembly.equivalence reorder)

def positiveSeven : Representation.Equiv (tensor.exteriorPower 7) positiveBranches.dual :=
  (SU3DoubleSpinExterior.complement (by rfl : 7+5=12)).trans (dualEquiv positive)

def negative : Representation.Equiv (dualTensor.exteriorPower 5) positiveBranches.dual :=
  (SU3DoubleSpinDuality.exterior 5).trans (dualEquiv positive)

def negativeSeven : Representation.Equiv (dualTensor.exteriorPower 7) positiveBranches :=
  (SU3DoubleSpinDuality.exterior 7).trans
    ((dualEquiv (SU3DoubleSpinExterior.complement (by rfl : 7+5=12))).trans
      (((bidualEquiv (tensor.exteriorPower 5)).symm).trans positive))

end
end Math.SU3DoubleSpinFifth
