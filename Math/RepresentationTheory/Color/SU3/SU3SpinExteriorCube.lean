import Math.RepresentationTheory.Exterior.ExteriorCubeDoublet
import Math.RepresentationTheory.Color.SU3.SU3ColorHook
import Math.RepresentationTheory.Color.SU3.SU3SpinExterior

/-! Complete actual SU3-color/SU2-spin cubic branching, with trace-free
endomorphisms retained as an actual representation. No irreducibility
claim for that representation is needed. -/
namespace Math.SU3SpinExteriorCube
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SU3SpinExterior
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
abbrev topBranch := spin.symmetricPower 3
abbrev middleBranch := external SU3ColorPair.adjoint WeakDoubletScalars.doublet

def hookEquiv : Representation.Equiv (ExteriorCubeHookRepresentation.action color)
    (SU3ColorPair.adjoint.comp (MonoidHom.fst _ _)) where
  toLinearEquiv := SU3ColorHook.equivalence.toLinearEquiv
  isIntertwining' g := SU3ColorHook.equivalence.isIntertwining' g.1

def middleEquiv : Representation.Equiv
    (ExteriorCubeDoubletRepresentation.middle color (MonoidHom.snd _ _)) middleBranch :=
  tensorEquiv hookEquiv (.refl spin)

/-- The middle exterior degree is exhausted by the spin-three top column
and the trace-free color/spin-one branch. -/
def cubeEquiv : Representation.Equiv (tensor.exteriorPower 3) (topBranch.prod middleBranch) :=
  (ExteriorCubeDoubletRepresentation.equivalence color (MonoidHom.snd _ _)
    SU3DefiningExterior.basis color_det).symm.trans
      (SplitRepresentationProjection.prodEquiv (.refl topBranch) middleEquiv)

end
end Math.SU3SpinExteriorCube
