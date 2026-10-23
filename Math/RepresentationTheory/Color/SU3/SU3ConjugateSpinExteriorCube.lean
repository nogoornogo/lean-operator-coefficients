import Math.RepresentationTheory.Exterior.ExteriorCubeDoublet
import Math.RepresentationTheory.Color.SU3.SU3DualColorHook
import Math.RepresentationTheory.Color.SU3.SU3ConjugateSpinExterior

/-! Complete actual dual-color/spin cubic branching. The color branch is
the trace-free endomorphism action on the dual defining color module. -/
namespace Math.SU3ConjugateSpinExteriorCube
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SU3ConjugateSpinExterior
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev topBranch := spin.symmetricPower 3
abbrev middleBranch := external (TraceEndomorphismSplit.traceFreeAction SU3DualExterior.rho)
  WeakDoubletScalars.doublet

def hookEquiv : Representation.Equiv (ExteriorCubeHookRepresentation.action color)
    ((TraceEndomorphismSplit.traceFreeAction SU3DualExterior.rho).comp (MonoidHom.fst _ _)) where
  toLinearEquiv := SU3DualColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3DualColorHook.equivalence.isIntertwining' g.1

def middleEquiv : Representation.Equiv
    (ExteriorCubeDoubletRepresentation.middle color (MonoidHom.snd _ _)) middleBranch :=
  tensorEquiv hookEquiv (.refl spin)

/-- Complete decomposition with the conjugate color action retained. -/
def cubeEquiv : Representation.Equiv (tensor.exteriorPower 3) (topBranch.prod middleBranch) :=
  (ExteriorCubeDoubletRepresentation.equivalence color (MonoidHom.snd _ _)
    SU3DualExterior.basis color_det).symm.trans
      (SplitRepresentationProjection.prodEquiv (.refl topBranch) middleEquiv)

end
end Math.SU3ConjugateSpinExteriorCube
