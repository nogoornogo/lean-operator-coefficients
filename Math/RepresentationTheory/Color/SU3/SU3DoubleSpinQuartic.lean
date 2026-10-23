import Math.RepresentationTheory.Color.Diagrams.ColorWeakQuartic
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinCubeResolved

/-! Q and conjugate-Q quartic and complementary branches. The two large
color/weak kernels are fully resolved into fixed color factors and weak
labels, with the independent spin action retained. -/
namespace Math.SU3DoubleSpinQuartic
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection SU3DoubleSpinSquare
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

abbrev positiveBranches := ColorWeakQuartic.quarticBranches color weakProjection spinProjection
abbrev negativeBranches := ColorWeakQuartic.quarticBranches color.dual weakProjection spinProjection

def colorHook : Representation.Equiv (ExteriorCubeHookRepresentation.action color)
    (ColorWeakQuartic.adjoint color) where
  toLinearEquiv := SU3ColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3ColorHook.equivalence.isIntertwining' g.1

def dualColorHook : Representation.Equiv (ExteriorCubeHookRepresentation.action color.dual)
    (ColorWeakQuartic.adjoint color.dual) where
  toLinearEquiv := SU3DualColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3DualColorHook.equivalence.isIntertwining' g.1

def positive : Representation.Equiv (tensor.exteriorPower 4) positiveBranches :=
  ColorWeakQuartic.quartic color weakProjection colorTwo SU3DefiningExterior.dimension
    SU3DoubleSpinExterior.color_det SU3DoubleSpinCubeResolved.colorTop colorHook
      dualColorTwo spinProjection

def negative : Representation.Equiv (dualTensor.exteriorPower 4) negativeBranches :=
  ColorWeakQuartic.quartic color.dual weakProjection
    (dualColorTwo.trans (bidualEquiv color))
    (by rw [Subspace.dual_finrank_eq, SU3DefiningExterior.dimension])
    SU3DoubleSpinExterior.dual_color_det SU3DoubleSpinCubeResolved.dualColorTop dualColorHook
    (((bidualEquiv color).symm.exteriorPower 2).trans colorTwo) spinProjection

def positiveEight : Representation.Equiv (tensor.exteriorPower 8) positiveBranches.dual :=
  (SU3DoubleSpinExterior.complement (by rfl : 8+4=12)).trans (dualEquiv positive)

def negativeEight : Representation.Equiv (dualTensor.exteriorPower 8) negativeBranches.dual :=
  (SU3DoubleSpinExterior.dualComplement (by rfl : 8+4=12)).trans (dualEquiv negative)

end
end Math.SU3DoubleSpinQuartic
